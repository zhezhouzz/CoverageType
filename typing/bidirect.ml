open Language
open Zutils
open Sugar
open Typectx

let value_type_infer _ _ = failwith "unimp"

let rec term_type_infer bctx (ctx : Nt.t rty ctx) (a : (Nt.t, Nt.t term) typed)
    : (Nt.t rty, Nt.t rty term) typed option =
  let () =
    Myconfig._log_typing @@ pprint_typing_infer ctx (layout_typed_term a, "??")
  in
  let res =
    match a.x with
    | CErr -> Some CErr #: (mk_bot_underrty a.ty)
    | CVal v ->
        let v = value_type_infer ctx v in
        Some (CVal v) #: v.ty
    | CApp _ | CAppOp _ ->
        let* bindings, res = term_type_infer_app ctx a in
        Some res.x #: (Auxtyping.exists_rty bindings res.ty)
    | CMatch { matched; match_cases } ->
        (* NOTE: we drop unreachable cases *)
        let match_cases =
          List.filter_map (match_case_type_infer ctx matched) match_cases
        in
        let unioned_ty =
          Auxtyping.union_rtys
          @@ List.map (function CMatchcase { exp; _ } -> exp.ty) match_cases
        in
        let matched = value_type_infer ctx matched in
        Some (CMatch { matched; match_cases }) #: unioned_ty
    | CLetDeTuple _ -> failwith "unimp"
    | CLetE { rhs; lhs; body } ->
        let* bindings, rhs = term_type_infer_app ctx rhs in
        let lhs = lhs.x #: rhs.ty in
        let bindings = bindings @ [ lhs ] in
        let* body = term_type_infer (add_to_rights ctx bindings) body in
        (* let _ = *)
        (*   Printf.printf "CLetE exists %s\n" *)
        (*   @@ List.split_by_comma (fun x -> x.x) bindings *)
        (* in *)
        Some
          (CLetE { rhs; lhs; body }) #: (Auxtyping.exists_rty bindings body.ty)
  in
  let result_text =
    match res with Some res -> layout_rty res.ty | None -> "None"
  in
  Myconfig._log_typing
  @@ pprint_typing_infer ctx (layout_typed_term a, result_text);
  res

and term_type_check bctx (ctx : Nt.t rty ctx) (y : (Nt.t, Nt.t term) typed)
    (rty : Nt.t rty) : (Nt.t rty, Nt.t rty term) typed option =
  let () =
    Myconfig._log_typing
    @@ pprint_typing_check ctx (layout_typed_term y, layout_rty rty)
  in
  match y.x with
  | CErr -> Some CErr #: rty
  | CLetDeTuple _ -> failwith "unimp"
  | CVal v ->
      let* v = value_type_check ctx v rty in
      Some (CVal v) #: rty
  | CApp _ | CAppOp _ | CMatch _ ->
      let* x = term_type_infer ctx y in
      (* let () = failwith "end" in *)
      if sub_rty_bool ctx (x.ty, rty) then Some x.x #: rty
      else (
        _warinning_subtyping_error __FILE__ __LINE__ (x.ty, rty);
        _warinning_typing_error __FILE__ __LINE__ (layout_typed_term y, rty);
        None)
  | CLetE { rhs; lhs; body } ->
      let* bindings, rhs = term_type_infer_app ctx rhs in
      let lhs = lhs.x #: rhs.ty in
      let bindings = bindings @ [ lhs ] in
      let* body = term_type_check (add_to_rights ctx bindings) body rty in
      (* let _ = *)
      (*   Printf.printf "CLetE exists %s\n" *)
      (*   @@ List.split_by_comma (fun x -> x.x) bindings *)
      (* in *)
      Some (CLetE { rhs; lhs; body }) #: rty
