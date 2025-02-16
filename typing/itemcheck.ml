open Language
open Zutils
open Bidirect
open Zdatatype

let _log = Myconfig._log_result

let _task_info name rty =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Check %s:@}\n" name;
  Pp.printf "@{<bold>check against with:@} %s\n" (layout_rty rty)

let _task_succ name =
  _log @@ fun _ ->
  Pp.printf "@{<bold>@{<yellow>Task %s, type check succeeded@}@}\n" name

let _task_fail name =
  _log @@ fun _ ->
  Pp.printf "@{<bold>@{<red>Task %s, type check failed@}@}\n" name

let item_check (bctx, imp_m) = function
  | MFuncImp { name; body; _ } ->
      let body = term_to_value body in
      Some (bctx, StrMap.add name.x body imp_m)
  | MRty { is_assumption = true; name; rty } ->
      Some (rty_add_to_right bctx name #: rty, imp_m)
  | MRty { is_assumption = false; name; rty } -> (
      let imp =
        StrMap.find
          (spf "The source code of given refinement type '%s' is missing." name)
          imp_m name
      in
      _assert [%here] "basic type" (Nt.equal_nt imp.ty (erase_rty rty));
      _task_info name rty;
      match value_type_check bctx (imp, rty) with
      | Some _ ->
          _task_succ name;
          Some (rty_add_to_right bctx name #: rty, imp_m)
      | None ->
          _task_fail name;
          None)
  | _ -> Some (bctx, imp_m)

let struc_check bctx items =
  let* bctx, _ =
    List.fold_left
      (fun res item ->
        let* bctx, imp_m = res in
        item_check (bctx, imp_m) item)
      (Some (bctx, StrMap.empty))
      items
  in
  Some bctx
