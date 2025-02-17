open Language
open Zutils
open PropTypecheck
open Typectx

type t = Nt.t

let _log = Myconfig._log_preprocess

let __force_typed loc = function
  | { ty = Nt.Ty_unknown; _ } -> _die loc
  | x -> x

let bi_typed_cty_check (ctx : t ctx) (cty : t cty) : t cty =
  let () =
    _log @@ fun _ ->
    pprint_ctx Nt.layout ctx;
    print_newline ();
    Printf.printf "cty: %s\n" (layout_cty cty)
  in
  match cty with
  | { phi; nty } ->
      let phi = bi_typed_prop_check (add_to_right ctx default_v #: nty) phi in
      { phi; nty }

let bi_typed_rty_check (ctx : t ctx) (rty : t rty) : t rty =
  let () = check_wf_rty rty in
  let rec aux ctx = function
    | RtyBase { ou; cty } -> RtyBase { ou; cty = bi_typed_cty_check ctx cty }
    | RtyArr { arr_type; argrty; arg; retty } ->
        let argrty = aux ctx argrty in
        let ctx' = add_to_right ctx arg #: (erase_rty argrty) in
        let retty = aux ctx' retty in
        RtyArr { arr_type; argrty; arg; retty }
    | RtyProd (r1, r2) -> RtyProd (aux ctx r1, aux ctx r2)
  in
  aux ctx rty

let rec bi_typed_term_infer (ctx : t ctx) (x : (t, t raw_term) typed) :
    (t, t raw_term) typed =
  match x.ty with
  | Nt.Ty_unknown -> bi_term_infer ctx x.x
  | _ -> bi_term_check ctx x.x x.ty

and bi_typed_term_check (ctx : t ctx) (x : (t, t raw_term) typed) (ty : t) :
    (t, t raw_term) typed =
  match x.ty with
  | Nt.Ty_unknown -> bi_term_check ctx x.x ty
  | _ ->
      let sndty = Nt._type_unify [%here] x.ty ty in
      bi_term_check ctx x.x sndty

and bi_term_check (ctx : t ctx) (x : t raw_term) (ty : t) :
    (t, t raw_term) typed =
  let () =
    _log @@ pprint_basic_typing (fun () -> pprint_ctx Nt.layout ctx) (x, ty)
  in
  match (x, ty) with
  | Err, _ -> Err #: ty
  | Const _, _ | Var _, _ ->
      let x = bi_term_infer ctx x in
      x.x #: (Nt._type_unify [%here] x.ty ty)
  | Tuple es, Ty_tuple tys ->
      let estys = _safe_combine [%here] es tys in
      let es = List.map (fun (e, ty) -> bi_typed_term_check ctx e ty) estys in
      (Tuple es) #: ty
  | Lam { lamarg; lambody }, Ty_arrow (t1, _) ->
      let lamarg = bi_typed_id_check ctx lamarg t1 in
      let ty = Nt._type_unify [%here] (Ty_arrow (lamarg.ty, Nt.Ty_any)) ty in
      let lambody =
        bi_typed_term_check (add_to_right ctx lamarg) lambody
          (snd @@ Nt.destruct_arr_tp ty)
      in
      (Lam { lamarg; lambody }) #: ty
  | AppOp (op, args), ty ->
      let op' = bi_typed_op_infer ctx op in
      let args' = List.map (bi_typed_term_infer ctx) args in
      let fty =
        Nt._type_unify [%here] op'.ty
          (Nt.construct_arr_tp (List.map _get_ty args', ty))
      in
      let argsty, _ = Nt.destruct_arr_tp fty in
      let args =
        List.map (fun (x, ty) -> bi_typed_term_check ctx x ty)
        @@ List.combine args argsty
      in
      let op = bi_typed_op_check ctx op fty in
      (AppOp (op, args)) #: ty
  | App (f, args), ty ->
      let f' = bi_typed_term_infer ctx f in
      let args' = List.map (bi_typed_term_infer ctx) args in
      let fty =
        Nt._type_unify [%here]
          (Nt.construct_arr_tp (List.map _get_ty args', ty))
          f'.ty
      in
      let argsty, _ = Nt.destruct_arr_tp fty in
      let args =
        List.map (fun (x, ty) -> bi_typed_term_check ctx x ty)
        @@ List.combine args argsty
      in
      let f = bi_typed_term_check ctx f fty in
      (App (f, args)) #: ty
  | Let { if_rec; rhs; lhs; letbody }, ty ->
      let lhs = List.map (__force_typed [%here]) lhs in
      let rhsty = Nt.Ty_tuple (List.map _get_ty lhs) in
      let rhs = bi_typed_term_check ctx rhs rhsty in
      let ctx' = add_to_rights ctx lhs in
      let ctx' =
        if if_rec then _failatwith [%here] "todo??"
          (* Typectx.add_to_right ctx ("f", construct_arr_tp (List.map xsty, ty)) *)
        else ctx'
      in
      let letbody = bi_typed_term_check ctx' letbody ty in
      (Let { if_rec; rhs; lhs; letbody }) #: ty
  | Ifte (e1, e2, e3), _ ->
      let e1 = bi_typed_term_check ctx e1 Nt.bool_ty in
      let e2 = bi_typed_term_check ctx e2 ty in
      let e3 = bi_typed_term_check ctx e3 ty in
      (Ifte (e1, e2, e3)) #: ty
  | Match { match_cases = []; _ }, _ ->
      _failatwith [%here] "bi_term_infer: pattern matching branch is empty"
  | Match { matched; match_cases }, _ ->
      let matched = bi_typed_term_infer ctx matched in
      let handle_case = function
        | Matchcase { constructor; args; exp } ->
            let constructor_ty =
              Nt.construct_arr_tp
                (List.map (fun _ -> Nt.Ty_any) args, matched.ty)
            in
            let constructor =
              bi_typed_id_check ctx constructor constructor_ty
            in
            let argsty, _ = Nt.destruct_arr_tp constructor.ty in
            let args =
              List.map (fun (x, ty) -> x.x #: ty)
              @@ _safe_combine [%here] args argsty
            in
            let ctx' = add_to_rights ctx args in
            let exp = bi_typed_term_check ctx' exp ty in
            Matchcase { constructor; args; exp }
      in
      let match_cases = List.map handle_case match_cases in
      (Match { matched; match_cases }) #: ty
  | e, ty ->
      _failatwith [%here]
        (spf "bi_term_check: inconsistent term (%s) and type (%s)"
           (layout_raw_term e) (Nt.layout ty))

and bi_term_infer (ctx : t ctx) (x : t raw_term) : (t, t raw_term) typed =
  match x with
  | Err ->
      failwith
        "Cannot infer the type of the exception, should provide the return type"
  | Const c -> (Const c) #: (constant_to_nt c)
  | Var id ->
      (* let _ = Printf.printf "id: %s\n" id.x in *)
      let id = bi_typed_id_infer ctx id in
      (Var id) #: id.ty
  | Tuple es ->
      let es = List.map (bi_typed_term_infer ctx) es in
      let ty = Nt.Ty_tuple (List.map _get_ty es) in
      (Tuple es) #: ty
  | Lam { lamarg; lambody } ->
      let lamarg = __force_typed [%here] lamarg in
      let lambody = bi_typed_term_infer (add_to_right ctx lamarg) lambody in
      let ty = Nt.construct_arr_tp ([ lamarg.ty ], lambody.ty) in
      (Lam { lamarg; lambody }) #: ty
  | AppOp (op, args) ->
      let args = List.map (bi_typed_term_infer ctx) args in
      let op =
        bi_typed_op_check ctx op
          (Nt.construct_arr_tp (List.map _get_ty args, Nt.Ty_any))
      in
      let _, ty = Nt.destruct_arr_tp op.ty in
      (AppOp (op, args)) #: ty
  | App (f, args) ->
      let f = bi_typed_term_infer ctx f in
      let argsty, ty = Nt.destruct_arr_tp f.ty in
      let args =
        List.map (fun (x, ty) -> bi_typed_term_check ctx x ty)
        @@ _safe_combine [%here] args argsty
      in
      (App (f, args)) #: ty
  | Let { if_rec = true; _ } ->
      _failatwith [%here] "cannot infer ret type of recursive function"
  | Let { if_rec; rhs; lhs; letbody } ->
      let lhs = List.map (__force_typed [%here]) lhs in
      let rhsty = Nt.Ty_tuple (List.map _get_ty lhs) in
      let rhs = bi_typed_term_check ctx rhs rhsty in
      let ctx' = add_to_rights ctx lhs in
      let ctx' =
        if if_rec then _failatwith [%here] "todo??"
          (* Typectx.add_to_right ctx ("f", construct_arr_tp (List.map xsty, ty)) *)
        else ctx'
      in
      let letbody = bi_typed_term_infer ctx' letbody in
      (Let { if_rec; rhs; lhs; letbody }) #: letbody.ty
  | Ifte (e1, e2, e3) ->
      let e1 = bi_typed_term_check ctx e1 Nt.bool_ty in
      let e2 = bi_typed_term_infer ctx e2 in
      let e3 = bi_typed_term_check ctx e3 e2.ty in
      (Ifte (e1, e2, e3)) #: e2.ty
  | Match { matched; match_cases } ->
      let matched = bi_typed_term_infer ctx matched in
      let handle_case = function
        | Matchcase { constructor; args; exp } ->
            let constructor_ty =
              Nt.construct_arr_tp
                (List.map (fun _ -> Nt.Ty_unknown) args, matched.ty)
            in
            let constructor =
              bi_typed_id_check ctx constructor constructor_ty
            in
            let argsty, _ = Nt.destruct_arr_tp constructor.ty in
            let args =
              List.map (fun (x, ty) -> x.x #: ty)
              @@ _safe_combine [%here] args argsty
            in
            let ctx' = add_to_rights ctx args in
            let exp = bi_typed_term_infer ctx' exp in
            Matchcase { constructor; args; exp }
      in
      let match_cases = List.map handle_case match_cases in
      let ty =
        match match_cases with
        | [] ->
            _failatwith [%here]
              "bi_term_infer: pattern matching branch is empty"
        | Matchcase { exp; _ } :: match_cases ->
            let ty = exp.ty in
            if
              List.for_all
                (function Matchcase { exp; _ } -> Nt.equal_nt exp.ty ty)
                match_cases
            then ty
            else
              _failatwith [%here]
                "bi_term_infer: pattern matching branchs have different types"
      in
      (Match { matched; match_cases }) #: ty

let typed_term_infer = bi_typed_term_infer
let typed_term_check = bi_typed_term_check

let constructor_declaration_mk_ (retty, { constr_name; argsty }) =
  constr_name #: (Nt.construct_arr_tp (argsty, retty))

let item_mk_ctx (e : t item) =
  match e with
  | MTyDecl { type_name; type_params; type_decls } ->
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs =
        List.map (fun c -> constructor_declaration_mk_ (retty, c)) type_decls
      in
      xs
  | MValDecl x -> [ __force_typed [%here] x ]
  | MMethodPred mp -> [ __force_typed [%here] mp ]
  | MAxiom _ -> []
  | MRty _ -> []
  | MFuncImpRaw _ | MFuncImp _ -> _failatwith [%here] "not predefine"

let item_erase (e : 'a item) =
  match e with
  | MRty { name; rty; _ } -> MValDecl name #: (Some (erase_rty rty))
  | _ -> e

let item_check ctx (e : t item) : t ctx * t item =
  match e with
  | MTyDecl { type_name; type_params; type_decls } ->
      let res = MTyDecl { type_name; type_params; type_decls } in
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs =
        List.map (fun c -> constructor_declaration_mk_ (retty, c)) type_decls
      in
      (add_to_rights ctx xs, res)
  | MValDecl x ->
      let x = __force_typed [%here] x in
      let res = MValDecl x in
      (add_to_right ctx x, res)
  | MMethodPred x ->
      let x = __force_typed [%here] x in
      let res = MMethodPred x in
      (add_to_right ctx x, res)
  | MAxiom { name; prop } ->
      (ctx, MAxiom { name; prop = bi_typed_prop_check ctx prop })
  | MRty { is_assumption; name; rty } ->
      let rty = bi_typed_rty_check ctx rty in
      let item = MRty { is_assumption; name; rty } in
      let ctx =
        if is_assumption then
          match get_opt ctx name with
          | Some rty' ->
              (* let () = *)
              (*   Printf.printf "%s =? %s ==> %b\n" (Nt.show_nt rty') *)
              (*     (Nt.show_nt (erase_rty rty)) *)
              (*     (Nt.equal_nt rty' (erase_rty rty)) *)
              (* in *)
              let _ = Nt._type_unify [%here] rty' (erase_rty rty) in
              ctx
          | None -> add_to_right ctx name #: (erase_rty rty)
        else ctx
      in
      (ctx, item)
  | MFuncImpRaw { name; if_rec = false; body } ->
      let body = bi_typed_term_infer ctx body in
      let name = name.x #: body.ty in
      (add_to_right ctx name, MFuncImpRaw { name; if_rec = false; body })
  | MFuncImpRaw { name; if_rec = true; body } ->
      let name_ty = __get_lam_term_ty [%here] body.x in
      let name = name.x #: name_ty in
      let ctx' = add_to_right ctx name in
      let body = bi_typed_term_check ctx' body name.ty in
      (ctx', MFuncImpRaw { name; if_rec = true; body })
  | MFuncImp _ -> _failatwith [%here] "die"

let struct_mk_basic_ctx ctx l =
  add_to_rights ctx @@ List.concat @@ List.map item_mk_ctx l

let struct_mk_rty_ctx l =
  let aux res = function
    | MRty { is_assumption = true; name; rty } ->
        Typectx.add_to_right res name #: rty
    | _ -> res
  in
  List.fold_left aux Typectx.emp l

let struct_mk_axiom_ctx l =
  let aux res = function
    | MAxiom { name; prop } -> Typectx.add_to_right res name #: prop
    | _ -> res
  in
  List.fold_left aux Typectx.emp l

let struct_check ctx l =
  List.fold_left
    (fun (ctx, res) e ->
      let ctx, e = item_check ctx e in
      (ctx, res @ [ e ]))
    (ctx, []) l
