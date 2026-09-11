open Language
open Zutils
open PropTypecheck
open Typectx
open Zdatatype

type t = Nt.t

let constraint_cty_type_check (ctx : t ctx) (bc : BC.bc) ({ phi; nty } : t cty)
    =
  let ctx = add_to_right ctx default_v#:nty in
  let bc, phi = constraint_prop_type_check ctx bc phi in
  (bc, { nty; phi })

let constraint_rty_type_check (ctx : t ctx) (bc : BC.bc) (rty : t rty) =
  let rec aux ctx bc rty =
    let () =
      TypecheckerLog.preprocess @@ fun _ ->
      Printf.printf "rty: %s\n" (layout_rty rty)
    in
    match rty with
    | RtyBase { ou; cty } ->
        let bc, cty = constraint_cty_type_check ctx bc cty in
        (bc, RtyBase { ou; cty })
    | RtyArr { argrty; arg; retty } ->
        let bc, argrty = aux ctx bc argrty in
        let argnty = erase_rty argrty in
        let ctx' =
          if Nt.is_base_tp argnty then add_to_right ctx arg#:argnty else ctx
        in
        let bc, retty = aux ctx' bc retty in
        (bc, RtyArr { argrty; arg; retty })
    | RtyPolyType { pt; rty } ->
        let bc = BC.add_type_var bc pt in
        let bc, rty = aux ctx bc rty in
        (bc, RtyPolyType { pt; rty })
    | RtyPolyPred { pred; rty } ->
        let ctx' = add_to_right ctx pred in
        let bc, rty = aux ctx' bc rty in
        (bc, RtyPolyPred { pred; rty })
  in
  aux ctx bc rty

(* let cty_type_check (ctx : t ctx) (poly_vars : string list) *)
(*     ({ phi; nty } : t cty) : t cty = *)
(*   let () = *)
(*     TypecheckerLog.preprocess @@ fun _ -> *)
(*     pprint_ctx Nt.layout ctx; *)
(*     print_newline (); *)
(*     Printf.printf "cty: %s\n" (layout_cty { phi; nty }) *)
(*   in *)
(*   { phi = prop_type_check (add_to_right ctx default_v#:nty) poly_vars phi; nty } *)

let rty_type_check (ctx : t ctx) (poly_vars : string list) (rty : t rty) : t rty
    =
  let () = check_syntactically_wf_rty rty in
  let () =
    TypecheckerLog.preprocess @@ fun _ ->
    pprint_ctx Nt.layout ctx;
    print_newline ();
    Pp.printf "@{<bold>rty task@}: %s\n" (layout_rty rty)
  in
  let bc, rty = constraint_rty_type_check ctx (BC.empty poly_vars) rty in
  let solution = Normalty.type_unification StrMap.empty bc.cs in
  match solution with
  | None ->
      Printf.printf "bc\n%s\nprop:%s\n" (BC.layout bc) (layout_rty rty);
      _die_with [%here] "rty normal type error"
  | Some sol -> map_rty (Normalty.msubst_nt sol) rty

module BC = Normalty.BoundConstraints

let rec constraint_term_type_infer (ctx : t ctx) (bc : BC.bc) (e : t raw_term) =
  match e with
  | Err ->
      let bc, t = BC.fresh bc in
      (* let () = Printf.printf "mk t: %s\n" (Nt.layout t) in *)
      (bc, Err#:t)
  | Const c -> (bc, (Const c)#:(constant_to_nt c))
  | Var id ->
      let bc, id = constraint_id_type_check ctx bc id in
      let () =
        TypecheckerLog.preprocess @@ fun _ ->
        Printf.printf "id: %s : %s\n" id.x (Nt.layout id.ty)
      in
      (bc, (Var id)#:id.ty)
  | Tuple es ->
      let bc, es = constraint_terms_type_check ctx bc es in
      (bc, (Tuple es)#:(Nt.Ty_tuple (List.map _get_ty es)))
  | Record es ->
      let es = List.sort (fun x y -> String.compare (fst x) (fst y)) es in
      let fields, es = List.split es in
      let bc, es = constraint_terms_type_check ctx bc es in
      let es = List.combine fields es in
      let tys = List.map (fun (x, e) -> x#:e.ty) es in
      (bc, (Record es)#:(Nt.mk_record None tys))
  | Field (e, field) ->
      let bc, e = constraint_term_type_check ctx bc e in
      let tys = Nt.as_record [%here] e.ty in
      let ty =
        _get_ty @@ List.find "die" (fun x -> String.equal x.x field) tys
      in
      (bc, (Field (e, field))#:ty)
  | Lam { lamarg; lambody } ->
      let lamarg = Nt.__force_typed [%here] lamarg in
      let bc, lambody =
        constraint_term_type_check (add_to_right ctx lamarg) bc lambody
      in
      let ty = Nt.construct_arr_tp ([ lamarg.ty ], lambody.ty) in
      (bc, (Lam { lamarg; lambody })#:ty)
  | AppOp (op, args) ->
      let bc, op = constraint_op_type_check ctx bc op in
      let () =
        TypecheckerLog.preprocess @@ fun () ->
        Printf.printf "op: %s : %s\n" (Prop.layout_op op.x) (Nt.layout op.ty)
      in
      let bc, args = constraint_terms_type_check ctx bc args in
      let bc, retty = BC.fresh bc in
      let op_ty = Nt.construct_arr_tp (List.map _get_ty args, retty) in
      (* let op_ty = *)
      (*   match args with *)
      (*   | [] -> retty *)
      (*   | _ -> *)
      (*       Nt.construct_arr_tp *)
      (*         ([ Nt.mk_tuple [%here] @@ List.map _get_ty args ], retty) *)
      (* in *)
      let bc, _ = BC.add bc (op_ty, op.ty) in
      (bc, (AppOp (op, args))#:retty)
  | App (f, args) ->
      let bc, f = constraint_term_type_check ctx bc f in
      let bc, args = constraint_terms_type_check ctx bc args in
      let bc, retty = BC.fresh bc in
      let f_ty = Nt.construct_arr_tp (List.map _get_ty args, retty) in
      let bc, _ = BC.add bc (f_ty, f.ty) in
      (bc, (App (f, args))#:retty)
  | Let { if_rec = false; rhs; lhs; letbody } ->
      let () =
        List.iter
          (fun x ->
            if Nt.is_unkown x.ty then
              _die_with [%here] (spf "let-binding %s is untyped" x.x))
          lhs
      in
      let bc, rhs = constraint_term_type_check ctx bc rhs in
      let bc, letbody =
        constraint_term_type_check (add_to_rights ctx lhs) bc letbody
      in
      let bc, _ = BC.add bc (Nt.Ty_tuple (List.map _get_ty lhs), rhs.ty) in
      (bc, (Let { if_rec = false; rhs; lhs; letbody })#:letbody.ty)
  | Let { if_rec = true; rhs; lhs = [ recf ]; letbody } ->
      _assert [%here] "recursive function doesn't typed"
        (Nt.equal_nt recf.ty Nt.Ty_unknown);
      let recf = recf.x#:(__get_lam_term_ty [%here] rhs.x) in
      let recf = Nt.__force_typed [%here] recf in
      let ctx' = add_to_right ctx recf in
      let bc, rhs = constraint_term_type_check ctx' bc rhs in
      let bc, letbody = constraint_term_type_check ctx' bc letbody in
      let bc, _ = BC.add bc (recf.ty, rhs.ty) in
      (bc, (Let { if_rec = true; rhs; lhs = [ recf ]; letbody })#:letbody.ty)
  | Let { if_rec = true; _ } -> _die [%here]
  | Ifte (e1, e2, e3) ->
      let bc, e1 = constraint_term_type_check ctx bc e1 in
      let bc, e2 = constraint_term_type_check ctx bc e2 in
      let bc, e3 = constraint_term_type_check ctx bc e3 in
      let bc, _ = BC.add bc (Nt.bool_ty, e1.ty) in
      let bc, (ty, _) = BC.add bc (e2.ty, e3.ty) in
      (bc, (Ifte (e1, e2, e3))#:ty)
  | Match { matched; match_cases } -> (
      let bc, matched = constraint_term_type_check ctx bc matched in
      let handle_case bc = function
        | Matchcase { constructor; args; exp } ->
            let bc, args =
              List.fold_right
                (fun x (bc, args) ->
                  let bc, t = BC.fresh bc in
                  (bc, (x.x#:t) :: args))
                args (bc, [])
            in
            let bc, op =
              constraint_op_type_infer ctx bc (DtConstructor constructor.x)
            in
            let constructor = constructor.x#:op.ty in
            let bc, exp =
              constraint_term_type_check (add_to_rights ctx args) bc exp
            in
            let constructor_ty =
              Nt.construct_arr_tp (List.map _get_ty args, matched.ty)
            in
            let bc, _ = BC.add bc (constructor_ty, constructor.ty) in
            (bc, (Matchcase { constructor; args; exp })#:exp.ty)
      in
      let bc, cases =
        List.fold_right
          (fun case (bc, cases) ->
            let bc, case = handle_case bc case in
            (bc, case :: cases))
          match_cases (bc, [])
      in
      match cases with
      | [] ->
          _die_with [%here] "bi_term_infer: pattern matching branch is empty"
      | case :: l ->
          let cases, tys =
            List.split @@ List.map (function { x; ty } -> (x, ty)) l
          in
          let bc =
            List.fold_right (fun ty bc -> fst @@ BC.add bc (case.ty, ty)) tys bc
          in
          (bc, (Match { matched; match_cases = case.x :: cases })#:case.ty))

and constraint_terms_type_check (ctx : t ctx) (bc : BC.bc)
    (lits : (t, t raw_term) typed list) =
  match lits with
  | [] -> (bc, [])
  | lit :: lits ->
      let bc, lits = constraint_terms_type_check ctx bc lits in
      let bc, lit = constraint_term_type_check ctx bc lit in
      (bc, lit :: lits)

and constraint_term_type_check (ctx : t ctx) (bc : BC.bc)
    (e : (t, t raw_term) typed) =
  mk_constraint e.ty (constraint_term_type_infer ctx bc e.x)

let raw_term_type_check ctx polyvars term =
  let bc, term = constraint_term_type_check ctx (BC.empty polyvars) term in
  let solution = Normalty.type_unification StrMap.empty bc.cs in
  match solution with
  | None ->
      let () =
        TypecheckerLog.preprocess @@ fun _ ->
        Pp.printf "@{<bold>Before subst:@}\n%s\n" (layout_typed_raw_term term)
      in
      _die_with [%here] "raw term normal type error"
  | Some sol ->
      let res = typed_map_raw_term (Normalty.msubst_nt sol) term in
      let () =
        TypecheckerLog.preprocess @@ fun _ ->
        Pp.printf "@{<bold>Before subst:@}\n%s\n" (layout_typed_raw_term term);
        Pp.printf "@{<bold>Solution:@}\n%s\n"
          (List.split_by_comma (fun (x, ty) -> spf "%s -> %s" x (Nt.layout ty))
          @@ StrMap.to_kv_list sol);
        Pp.printf "@{<bold>After subst:@}\n%s\n"
          (show_raw_term
             (fun format t ->
               OcamlParser.Pprintast.core_type format (Nt.t_to_core_type t))
             res.x)
      in
      res

let constructor_declaration_mk_ (retty, { constr_name; argsty }) =
  constr_name#:(Nt.close_poly_nt [%here] @@ Nt.construct_arr_tp (argsty, retty))

let item_mk_ctx (e : t item) =
  match e with
  | MTyDecl { type_name; type_params; type_decl = Decl_constructors l } ->
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs = List.map (fun c -> constructor_declaration_mk_ (retty, c)) l in
      xs
  | MTyDecl { type_decl = Decl_record _; _ } -> []
  | MValDecl x -> [ Nt.__force_typed [%here] x ]
  | MMethodPred mp -> [ Nt.__force_typed [%here] mp ]
  | MAxiom _ -> []
  | MRty _ -> []
  | MLocalRty _ -> []
  | MFuncImpRaw _ | MFuncImp _ -> _failatwith [%here] "not predefine"

let item_erase (e : 'a item) =
  match e with
  | MRty { name; rty; _ } -> MValDecl name#:(Some (erase_rty rty))
  | _ -> e

let item_check (checked : t item list) ctx (e : t item) : t ctx * t item =
  match e with
  | MTyDecl { type_name; type_params; type_decl = Decl_constructors fds } ->
      let res =
        MTyDecl { type_name; type_params; type_decl = Decl_constructors fds }
      in
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs = List.map (fun c -> constructor_declaration_mk_ (retty, c)) fds in
      (add_to_rights ctx xs, res)
  | MTyDecl { type_decl = Decl_record _; _ } -> (ctx, e)
  | MValDecl x ->
      let x = Nt.__force_typed [%here] x in
      let res = MValDecl x in
      (add_to_right ctx x, res)
  | MMethodPred x ->
      let x = Nt.__force_typed [%here] x in
      let res = MMethodPred x in
      (add_to_right ctx x, res)
  | MAxiom { name; tasks; prop } ->
      (ctx, MAxiom { name; tasks; prop = prop_type_check ctx [ "a" ] prop })
  | MLocalRty { host_name; name; rty; captured } ->
      let host_rty =
        List.filter_map
          (function
            | MRty { name; rty; _ } ->
                if String.equal name host_name then Some rty else None
            | _ -> None)
          checked
      in
      let host_rty = match host_rty with [ rty ] -> rty | _ -> _die [%here] in
      let poly_vars, host_rty = lift_poly_rty host_rty in
      let preds, _ = lift_poly_pred_rty host_rty in
      let ctx' = add_to_rights ctx preds in
      let rty = rty_type_check ctx' poly_vars rty in
      let item = MLocalRty { host_name; name; rty; captured } in
      (ctx, item)
  | MRty { is_assumption; name; rty } ->
      let rty = rty_type_check ctx [] rty in
      let item = MRty { is_assumption; name; rty } in
      let ctx =
        if is_assumption then
          match get_opt ctx name with
          | Some _ -> ctx
          | None -> add_to_right ctx name#:(erase_rty rty)
        else ctx
      in
      (ctx, item)
  | MFuncImpRaw { name; if_rec = false; body } ->
      let pt, t = Nt.lift_poly_tp body.ty in
      let body = raw_term_type_check ctx pt body.x#:t in
      let body = body.x#:(Nt.construct_poly_nt (pt, t)) in
      (add_to_right ctx name, MFuncImpRaw { name; if_rec = false; body })
  | MFuncImpRaw { name; if_rec = true; body } ->
      let ctx' = add_to_right ctx name in
      let pt, t = Nt.lift_poly_tp body.ty in
      let body = raw_term_type_check ctx' pt body.x#:t in
      let body = body.x#:(Nt.construct_poly_nt (pt, t)) in
      (ctx', MFuncImpRaw { name; if_rec = true; body })
  | MFuncImp _ -> _failatwith [%here] "die"

let struct_mk_basic_ctx ctx l =
  add_to_rights ctx @@ List.concat @@ List.map item_mk_ctx l

let struct_mk_rty_ctx l =
  let aux res = function
    | MRty { is_assumption = true; name; rty } ->
        Typectx.add_to_right res name#:rty
    | _ -> res
  in
  List.fold_left aux Typectx.emp l

let struct_mk_axiom_ctx l =
  let aux res = function
    | MAxiom { name; tasks; prop } -> res @ [ (name, tasks, prop) ]
    | _ -> res
  in
  List.fold_left aux [] l

let struct_check ctx l =
  List.fold_left
    (fun (ctx, res) e ->
      let ctx, e = item_check res ctx e in
      (ctx, res @ [ e ]))
    (ctx, []) l
