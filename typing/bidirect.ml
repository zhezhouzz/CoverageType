open Language
open Zutils
open Sugar
open Auxtyping
open Common

let type_check_group (bctx : built_in_ctx) =
  let _id_type_infer loc (rctx : rctx) (id : string) : Nt.t rty =
    let res = lookup_ctxs [ rctx.ctx; rctx.gctx; bctx.builtin_ctx ] id in
    let rty =
      match res with
      | Some res -> res
      | None -> _failatwith loc (spf "cannot find %s in type context" id)
    in
    let rty =
      match rty with
      (* NOTE: both over and under type will induce under type *)
      | RtyBase { cty; _ } -> mk_eq_tvar_underrty id #: (erase_cty cty)
      | RtyArr _ -> rty
      | RtyProd _ -> _failatwith [%here] "unimp"
    in
    rty
  in
  let rec value_type_infer (rctx : rctx) (v : (Nt.t, Nt.t value) typed) :
      (Nt.t rty, Nt.t rty value) typed =
    let res =
      match v.x with
      | VVar id ->
          let rty = _id_type_infer [%here] rctx id.x in
          (VVar id.x #: rty) #: rty
      | VConst U -> (VConst U) #: (mk_bot_underrty Nt.Ty_unit)
      | VConst c -> (VConst c) #: (mk_eq_c_underrty c)
      | VLam _ | VFix _ | VTuple _ -> _failatwith [%here] "unimp"
    in
    _assert [%here] "basic type inconsistent"
    @@ Nt.equal_nt (erase_rty res.ty) v.ty;
    pprint_typing_infer_value_after rctx (v, Some res.ty);
    res
  and value_type_check (rctx : rctx) (v : (Nt.t, Nt.t value) typed)
      (rty : Nt.t rty) : (Nt.t rty, Nt.t rty value) typed option =
    let () = pprint_typing_check_value rctx (v, rty) in
    match (v.x, rty) with
    | _, RtyArr { arr_type = GhostOverBaseArr; argrty; arg; retty } ->
        value_type_check (rctx_add_gvar rctx arg #: argrty) v retty
    | VConst _, _ | VVar _, _ ->
        let e = value_type_infer rctx v in
        if sub_rty bctx (rctx_to_ctx rctx) (e.ty, rty) then Some e
        else (
          _warinning_subtyping_error [%here] (e.ty, rty);
          _warinning_typing_error [%here] (layout_typed_value v, rty);
          None)
    | VLam { lamarg; body }, RtyArr { arr_type = NormalArr; argrty; arg; retty }
      ->
        (* Note: unify the name of parameter type and lambda variable *)
        let retty = subst_rty_instance arg (AVar lamarg) retty in
        let rctx', lamarg = rctx_add_var rctx lamarg.x #: argrty in
        let* body = term_type_check rctx' body retty in
        Some
          (VLam { lamarg; body })
          #: (RtyArr { arr_type = NormalArr; argrty; arg; retty })
    | VLam _, _ -> _die [%here]
    | VFix _, _ -> _failatwith [%here] "unimp"
    (* | VFix { fixname; fixarg; body }, RtyBaseArr { argcty; arg; retty } -> *)
    (*     let _, ret_nty = Nt.destruct_arr_tp fixname.ty in *)
    (*     (\* For STLC, we use a different recursion template *\) *)
    (*     if String.equal "stlc_term" (layout_ty ret_nty) then *)
    (*       match (body.x, retty) with *)
    (*       | ( CVal { x = VLam { lamarg; body }; _ }, *)
    (*           RtyBaseArr { argcty = argcty1; arg = arg1; retty } ) -> *)
    (*           let rty' = *)
    (*             let arg' = { x = Rename.unique arg; ty = fixarg.ty } in *)
    (*             let arg = arg #: fixarg.ty in *)
    (*             let arg1' = { x = Rename.unique arg1; ty = lamarg.ty } in *)
    (*             let arg1 = arg1 #: lamarg.ty in *)
    (*             let rec_constraint_cty = apply_rec_arg2 arg arg' arg1 in *)
    (*             RtyBaseArr *)
    (*               { *)
    (*                 argcty; *)
    (*                 arg = arg'.x; *)
    (*                 retty = *)
    (*                   RtyBaseArr *)
    (*                     { *)
    (*                       argcty = *)
    (*                         intersect_ctys [ argcty1; rec_constraint_cty ]; *)
    (*                       arg = arg1'.x; *)
    (*                       retty = *)
    (*                         subst_rty_instance arg1.x (AVar arg1') *)
    (*                         @@ subst_rty_instance arg.x (AVar arg') retty; *)
    (*                     }; *)
    (*               } *)
    (*           in *)
    (*           let binding = arg #: (RtyBase { ou = true; cty = argcty }) in *)
    (*           let binding1 = arg1 #: (RtyBase { ou = true; cty = argcty1 }) in *)
    (*           let body = *)
    (*             body *)
    (*             #-> (subst_term_instance fixarg.x (VVar arg #: fixarg.ty)) *)
    (*             #-> (subst_term_instance lamarg.x (VVar arg1 #: fixarg.ty)) *)
    (*           in *)
    (*           let* body' = *)
    (*             term_type_check *)
    (*               (add_to_rights ctx [ binding; binding1; fixname.x #: rty' ]) *)
    (*               body retty *)
    (*           in *)
    (*           let lam = *)
    (*             (VLam { lamarg = binding1; body = body' }) *)
    (*             #: (RtyBaseArr { argcty = argcty1; arg = arg1; retty }) *)
    (*           in *)
    (*           let clam = (CVal lam) #: lam.ty in *)
    (*           Some *)
    (*             (VFix *)
    (*                { fixname = fixname.x #: rty; fixarg = binding; body = clam }) *)
    (*             #: rty *)
    (*       | _ -> _failatwith [%here] "die" *)
    (*     else *)
    (*       let rec_constraint_cty = apply_rec_arg1 arg #: fixarg.ty in *)
    (*       let () = init_cur_rec_func_name (fixname.x, rec_constraint_cty) in *)
    (*       let rty' = *)
    (*         let a = { x = Rename.unique arg; ty = fixarg.ty } in *)
    (*         RtyBaseArr *)
    (*           { *)
    (*             argcty = intersect_ctys [ argcty; rec_constraint_cty ]; *)
    (*             arg = a.x; *)
    (*             retty = subst_rty_instance arg (AVar a) retty; *)
    (*           } *)
    (*       in *)
    (*       let binding = arg #: (RtyBase { ou = true; cty = argcty }) in *)
    (*       let body = *)
    (*         body #-> (subst_term_instance fixarg.x (VVar arg #: fixarg.ty)) *)
    (*       in *)
    (*       let* body' = *)
    (*         term_type_check *)
    (*           (add_to_rights ctx [ binding; fixname.x #: rty' ]) *)
    (*           body retty *)
    (*       in *)
    (*       Some *)
    (*         (VFix { fixname = fixname.x #: rty; fixarg = binding; body = body' }) *)
    (*         #: rty *)
    (* | VFix _, _ -> _die [%here] *)
    | VTuple _, _ -> _die [%here]
  and term_type_infer (rctx : rctx) (e : (Nt.t, Nt.t term) typed) :
      (Nt.t rty, Nt.t rty term) typed option =
    let () = pprint_typing_infer_term_before rctx e in
    let res =
      match e.x with
      | CErr -> Some CErr #: (mk_bot_underrty e.ty)
      | CVal v ->
          let v = value_type_infer rctx v in
          Some (CVal v) #: v.ty
      | CApp _ | CAppOp _ -> _die [%here]
      | CMatch { matched; match_cases } ->
          (* NOTE: we drop unreachable cases *)
          let match_cases =
            List.filter_map (match_case_type_infer rctx matched) match_cases
          in
          let unioned_ty =
            union_rtys
            @@ List.map (function CMatchcase { exp; _ } -> exp.ty) match_cases
          in
          let matched = value_type_infer rctx matched in
          Some (CMatch { matched; match_cases }) #: unioned_ty
      | CLetDeTuple _ -> failwith "unimp"
      | CLetE { rhs; lhs; body } ->
          let* rhs = term_type_infer rctx rhs in
          let rctx', lhs = rctx_add_var rctx lhs.x #: rhs.ty in
          let* body = term_type_infer rctx' body in
          Some
            (CLetE { rhs; lhs; body })
            #: (rctx_diff_exists_rty [%here] rctx' rctx body.ty)
    in
    pprint_typing_infer_term_after rctx
      ( e,
        let* res = res in
        Some res.ty );
    res
  and term_type_check (rctx : rctx) (e : (Nt.t, Nt.t term) typed)
      (rty : Nt.t rty) : (Nt.t rty, Nt.t rty term) typed option =
    let () = pprint_typing_check_term rctx (e, rty) in
    match e.x with
    | CErr -> Some CErr #: rty
    | CLetDeTuple _ -> failwith "unimp"
    | CVal v ->
        let* v = value_type_check rctx v rty in
        Some (CVal v) #: v.ty
    | CApp _ | CAppOp _ | CMatch _ ->
        let* e' = term_type_infer rctx e in
        if sub_rty bctx (rctx_to_ctx rctx) (e'.ty, rty) then Some e'.x #: rty
        else (
          _warinning_subtyping_error [%here] (e'.ty, rty);
          _warinning_typing_error [%here] (layout_typed_term e, rty);
          None)
    | CLetE { rhs; lhs; body } ->
        let* rhs = term_type_infer rctx rhs in
        let rctx', lhs = rctx_add_var rctx lhs.x #: rhs.ty in
        let* body = term_type_check rctx' body rty in
        Some (CLetE { rhs; lhs; body }) #: rty
  and match_case_type_infer _ _ _ =
    _failatwith [%here] "unimp"
    (* and match_case_type_infer (rctx : rctx) (matched : (Nt.t, Nt.t value) typed) *)
    (*     (x : Nt.t match_case) : Nt.t rty match_case option = *)
    (*   match x with *)
    (*   | CMatchcase { constructor; args; exp } -> *)
    (*       let constructor_rty = *)
    (*         _id_type_infer [%here] ctx (dt_name_for_typectx constructor.x) *)
    (*       in *)
    (*       let args, retty = *)
    (*         List.fold_left *)
    (*           (fun (args, rty) x -> *)
    (*             match rty with *)
    (*             | RtyBaseArr { argcty; arg; retty } -> *)
    (*                 let retty = subst_rty_instance arg (AVar x) retty in *)
    (*                 let x = x.x #: (RtyBase { ou = false; cty = argcty }) in *)
    (*                 (args @ [ x ], retty) *)
    (*             | RtyArrArr { argrty; retty } -> *)
    (*                 let x = x.x #: argrty in *)
    (*                 (args @ [ x ], retty) *)
    (*             | _ -> _failatwith [%here] "die") *)
    (*           ([], constructor_rty) args *)
    (*       in *)
    (*       let retty = *)
    (*         match retty with *)
    (*         | RtyBase { ou = false; cty = Cty { phi; _ } } -> *)
    (*             let lit = Checkaux.typed_value_to_typed_lit [%here] matched in *)
    (*             let phi = subst_prop_instance default_v lit.x phi in *)
    (*             RtyBase { ou = false; cty = Cty { nty = Nt.unit_ty; phi } } *)
    (*         | _ -> _failatwith [%here] "die" *)
    (*       in *)
    (*       let dummy = (Rename.unique "dummy") #: retty in *)
    (*       let bindings = args @ [ dummy ] in *)
    (*       let* exp = term_type_infer (add_to_rights ctx bindings) exp in *)
    (*       (\* let _ = *\) *)
    (*       (\*   Printf.printf "exists %s\n" *\) *)
    (*       (\*   @@ List.split_by_comma (fun x -> x.x) bindings *\) *)
    (*       (\* in *\) *)
    (*       let exp = exp.x #: (exists_rtys_to_rty bindings exp.ty) in *)
    (*       Some *)
    (*         (CMatchcase *)
    (*            { constructor = constructor.x #: constructor_rty; args; exp }) *)
  in
  (value_type_check, term_type_check)
