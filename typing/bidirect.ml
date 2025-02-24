open Language
open Zutils
open Sugar
open Auxtyping
open Common
open Rctx

let instantiate_arrow_rty _ _ _ = failwith "unimp"

let type_check_group (bctx : built_in_ctx) =
  let _id_type_infer loc (rctx : rctx) (id : string) : Nt.t rty =
    let res = lookup_ctxs [ Rctx.to_ctx rctx; bctx.builtin_ctx ] id in
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
      | VConst U -> (VConst U) #: (mk_bot_underrty Nt.unit_ty)
      | VConst c -> (VConst c) #: (mk_eq_c_underrty c)
      | VTuple vs ->
          let vs = List.map (value_type_infer rctx) vs in
          let phis =
            List.mapi
              (fun idx x ->
                match x.ty with
                | RtyBase { ou = Under; cty = { phi; _ } } ->
                    let y =
                      mk_nth_lit [%here] (AVar default_v #: v.ty) #: v.ty idx
                    in
                    let phi = subst_prop_instance default_v y.x phi in
                    phi
                | _ -> _failatwith [%here] "unimp")
              vs
          in
          let rty =
            RtyBase { ou = Under; cty = { nty = v.ty; phi = smart_and phis } }
          in
          (VTuple vs) #: rty
      | VLam _ | VFix _ -> _failatwith [%here] "unimp"
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
        value_type_check (Rctx.add_var rctx arg #: argrty) v retty
    | VConst _, _ | VVar _, _ | VTuple _, _ ->
        let e = value_type_infer rctx v in
        if sub_rty bctx (Rctx.to_ctx rctx) (e.ty, rty) then Some e
        else (
          _warinning_subtyping_error [%here] (e.ty, rty);
          _warinning_typing_error [%here] (layout_typed_value v, rty);
          None)
    | VLam { lamarg; body }, RtyArr { arr_type = NormalArr; argrty; arg; retty }
      ->
        (* Note: unify the name of parameter type and lambda variable *)
        let retty = subst_rty_instance arg (AVar lamarg) retty in
        let lamarg = lamarg.x #: argrty in
        let rctx' = Rctx.add_var rctx lamarg in
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
  (*       | _ -> _die [%here] *)
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
  and arrow_type_apply (rctx : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty option =
    let arr_type, argrty, arg, retty =
      match appf_rty with
      | RtyArr { arr_type; argrty; arg; retty } -> (arr_type, argrty, arg, retty)
      | _ -> _die [%here]
    in
    match arr_type with
    | GhostOverBaseArr ->
        let gvars, appf_rty = instantiate_arrow_rty rctx appf_rty apparg in
        let* res = arrow_type_apply rctx appf_rty apparg in
        Some (construct_grty gvars res)
    | NormalArr -> (
        let () =
          _assert [%here] "application basic type check"
            (Nt.equal_nt (erase_rty argrty) (erase_rty apparg.ty))
        in
        match argrty with
        | RtyBase { ou = Over; cty } ->
            let arglit = value_to_lit [%here] apparg.x in
            let retty = subst_rty_instance arg arglit retty in
            let tmp_rty =
              mk_unit_underrty (subst_prop_instance default_v arglit cty.phi)
            in
            if not (non_emptiness_rty bctx (Rctx.to_ctx rctx) tmp_rty) then (
              _warinning_nonemptiness_error [%here] argrty;
              _warinning_typing_error [%here] (layout_lit arglit, argrty);
              None)
            else
              let retty = exists_rty (Rename.unique "dummy") #: tmp_rty retty in
              Some retty
        | RtyBase { ou = Under; cty } ->
            let arglit =
              value_to_lit [%here] @@ _get_x @@ (apparg #=> erase_rty)
            in
            let retty = subst_rty_instance arg arglit retty in
            if not (sub_rty bctx (Rctx.to_ctx rctx) (apparg.ty, argrty)) then (
              _warinning_subtyping_error [%here] (apparg.ty, argrty);
              _warinning_typing_error [%here] (layout_lit arglit, argrty);
              None)
            else
              let gvar =
                (Rename.unique "dummy") #: (RtyBase { ou = Over; cty })
              in
              let tmp_rty =
                mk_unit_underrty
                  (lit_to_prop
                     (mk_lit_eq_lit [%here] (AVar gvar #=> erase_rty) arglit))
              in
              let retty = exists_rty (Rename.unique "dummy") #: tmp_rty retty in
              let retty = construct_grty [ gvar ] retty in
              Some retty
        | RtyArr _ ->
            if not (sub_rty bctx (Rctx.to_ctx rctx) (apparg.ty, argrty)) then (
              _warinning_subtyping_error [%here] (apparg.ty, argrty);
              _warinning_typing_error [%here]
                (layout_typed_value @@ (apparg #=> erase_rty), argrty);
              None)
            else (
              _assert [%here] "arrow typed variable cannot be refered"
                (is_free_rty arg retty);
              Some retty)
        | RtyProd _ -> _die [%here])
  and term_type_infer (rctx : rctx) (e : (Nt.t, Nt.t term) typed) :
      (Nt.t rty, Nt.t rty term) typed option =
    let () = pprint_typing_infer_term_before rctx e in
    let res =
      match e.x with
      | CErr -> Some CErr #: (mk_bot_underrty e.ty)
      | CVal v ->
          let v = value_type_infer rctx v in
          Some (CVal v) #: v.ty
      | CApp { appf; apparg } ->
          let appf, apparg' = map2 (value_type_infer rctx) (appf, apparg) in
          let* retty = arrow_type_apply rctx appf.ty apparg.x #: apparg'.ty in
          Some (CApp { appf; apparg = apparg' }) #: retty
      | CAppOp { op; appopargs } ->
          let op =
            op #=> (fun _ ->
            _id_type_infer [%here] rctx (op_name_for_typectx op.x))
          in
          let appopargs =
            List.map (fun v -> (v, value_type_infer rctx v)) appopargs
          in
          let* retty =
            List.fold_left
              (fun res (apparg, apparg') ->
                let* rty = res in
                arrow_type_apply rctx rty apparg.x #: apparg'.ty)
              (Some op.ty) appopargs
          in
          Some (CAppOp { op; appopargs = List.map snd appopargs }) #: retty
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
          let lhs = lhs.x #: rhs.ty in
          let rctx' = Rctx.add_var rctx lhs in
          let* body = term_type_infer rctx' body in
          Some
            (CLetE { rhs; lhs; body })
            #: (Rctx.diff_exists_rty [%here] rctx' rctx body.ty)
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
    | CApp _ | CAppOp _ | CMatch _ | CLetE _ ->
        let* e' = term_type_infer rctx e in
        if sub_rty bctx (Rctx.to_ctx rctx) (e'.ty, rty) then Some e'.x #: rty
        else (
          _warinning_subtyping_error [%here] (e'.ty, rty);
          _warinning_typing_error [%here] (layout_typed_term e, rty);
          None)
  (* | CLetE { rhs; lhs; body } -> *)
  (*     let* rhs = term_type_infer rctx rhs in *)
  (*     let rctx', lhs = Rctx.add_var rctx lhs.x #: rhs.ty in *)
  (*     let* body = term_type_check rctx' body rty in *)
  (*     Some (CLetE { rhs; lhs; body }) #: rty *)
  and match_case_type_infer (rctx : rctx) (matched : (Nt.t, Nt.t value) typed)
      (x : Nt.t match_case) : Nt.t rty match_case option =
    match x with
    | CMatchcase { constructor; args; exp } ->
        let constructor_rty =
          match lookup_ctxs [ bctx.builtin_ctx ] constructor.x with
          | Some rty -> rty
          | None ->
              _failatwith [%here]
              @@ spf "cannot find rty of constructor %s from builtin context"
                   constructor.x
        in
        (* let () = *)
        (*   Printf.printf "%s: %s\n" constructor.x (layout_rty constructor_rty) *)
        (* in *)
        let args, retty =
          List.fold_left
            (fun (args, rty) x ->
              match rty with
              | RtyArr { arr_type = NormalArr; argrty; arg; retty } ->
                  let retty = subst_rty_instance arg (AVar x) retty in
                  (args @ [ x.x #: argrty ], retty)
              | _ -> _die [%here])
            ([], constructor_rty) args
        in
        let retty =
          match retty with
          | RtyBase { ou = Under; cty = { phi; _ } } ->
              let phi =
                subst_prop_instance default_v
                  (value_to_lit [%here] matched.x)
                  phi
              in
              RtyBase { ou = Under; cty = { nty = Nt.unit_ty; phi } }
          | _ -> _die [%here]
        in
        let rctx' =
          Rctx.add_vars rctx (args @ [ (Rename.unique "dummy") #: retty ])
        in
        let* exp = term_type_infer rctx' exp in
        let exp = exp.x #: (Rctx.diff_exists_rty [%here] rctx' rctx exp.ty) in
        Some
          (CMatchcase
             { constructor = constructor.x #: constructor_rty; args; exp })
  in
  (value_type_check, term_type_check)

let value_type_check bctx (value, rty) =
  (fst @@ type_check_group bctx) Rctx.emp value rty

let term_type_check bctx (value, rty) =
  (snd @@ type_check_group bctx) Rctx.emp value rty
