open Language
open Zutils
open Zdatatype

type constructor_type = string list * Nt.nt

let layout_constructor_type x =
  spf "%s (%s) = %s" x.x (StrList.to_string (fst x.ty)) (Nt.layout (snd x.ty))

let layout_alias l = split_by "\n" layout_constructor_type l

let inline_record { x; ty = args, record_ty } ty =
  let f ts =
    let m = StrMap.of_list @@ _safe_combine [%here] args ts in
    let record_ty = Nt.msubst_nt m record_ty in
    record_ty
  in
  let ty = Nt.subst_constructor_nt (x, f) ty in
  let core =
    match record_ty with
    | Nt.Ty_record { alias; fds } -> (List.map _get_x fds, alias)
    | _ -> _die [%here]
  in
  Nt.subst_alias_in_record_nt core ty

let self_inline l =
  let rec aux l =
    match l with
    | [] -> []
    | decl :: l ->
        let l =
          List.map
            (fun { x; ty = args, record_ty } ->
              { x; ty = (args, inline_record decl record_ty) })
            l
        in
        decl :: aux l
  in
  aux l

let item_mk_type_alias_ctx items =
  let f e =
    match e with
    | MTyDecl { type_name; type_params; type_decl = Decl_record fds } ->
        let record_type = Nt.mk_record (Some type_name) fds in
        [ type_name#:(type_params, record_type) ]
    | MTyDecl _ -> []
    | MValDecl _ -> []
    | MMethodPred _ -> []
    | MAxiom _ -> []
    | MRty _ -> []
    | MLocalRty _ -> []
    | MFuncImpRaw _ | MFuncImp _ -> []
  in
  let l = List.concat_map f items in
  self_inline l

let item_inline decls items =
  let inline nt =
    let res = List.fold_right inline_record decls nt in
    let () =
      TypecheckerLog.inline @@ fun () ->
      Printf.printf "decls %s \n" (List.split_by_comma _get_x decls);
      Printf.printf "inline %s ==> %s\n" (Nt.layout nt) (Nt.layout res)
    in
    res
  in
  let f e =
    match e with
    | MTyDecl { type_name; type_params; type_decl = Decl_constructors decls } ->
        let decls =
          List.map
            (fun { constr_name; argsty } ->
              { constr_name; argsty = List.map inline argsty })
            decls
        in
        let res =
          MTyDecl
            { type_name; type_params; type_decl = Decl_constructors decls }
        in
        Some res
    | MTyDecl { type_name; type_params; type_decl = Decl_record fds } ->
        (* if List.exists (fun x -> String.equal type_name x.x) decls then Some e *)
        (* else *)
        let fds = List.map (fun x -> x#=>inline) fds in
        let res =
          MTyDecl { type_name; type_params; type_decl = Decl_record fds }
        in
        Some res
    | MValDecl x -> Some (MValDecl x#=>inline)
    | MMethodPred x -> Some (MMethodPred x#=>inline)
    | MAxiom { name; tasks; prop } ->
        Some (MAxiom { name; tasks; prop = map_prop inline prop })
    | MLocalRty { host_name; name; rty; captured } ->
        let rty = map_rty inline rty in
        Some (MLocalRty { host_name; name; rty; captured })
    | MRty { is_assumption; name; rty } ->
        let rty = map_rty inline rty in
        Some (MRty { is_assumption; name; rty })
    | MFuncImpRaw { name; if_rec; body } ->
        let name = name#=>inline in
        let body = typed_map_raw_term inline body in
        Some (MFuncImpRaw { name; if_rec; body })
    | MFuncImp _ -> _failatwith [%here] "die"
  in
  List.filter_map f items

(* let%test "inline_alias" = *)
(*   let () = *)
(*     ZUtilsConfig.meta_config_path := *)
(*       "/Users/zhezzhou/workspace/CoverageType/meta-config.json" *)
(*   in *)
(*   let test_file = *)
(*     "/Users/zhezzhou/workspace/CoverageType/data/inline_test/alias.ml" *)
(*   in *)
(*   let items = *)
(*     ocaml_structure_to_items *)
(*     @@ OcamlParser.Oparse.parse_imp_from_file ~sourcefile:test_file *)
(*   in *)
(*   let () = Pp.printf "@{<bold>Parse:@}\n%s\n" (layout_structure items) in *)
(*   let alias = item_mk_type_alias_ctx items in *)
(*   let items = item_inline alias items in *)
(*   let () = Pp.printf "@{<bold>Result:@}\n%s\n" (layout_structure items) in *)
(*   false *)
