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

let mk_imp_m bctx items =
  List.fold_left
    (fun (bctx, imp_m) item ->
      match item with
      | MFuncImp { name; body; _ } ->
          let body = term_to_value body in
          (bctx, StrMap.add name.x body imp_m)
      | MRty { is_assumption = true; name; rty } ->
          (rty_add_to_right bctx name #: rty, imp_m)
      | _ -> (bctx, imp_m))
    (bctx, StrMap.empty) items

let mk_tasks items =
  List.filter_map
    (function
      | MRty { is_assumption = false; name; rty } -> Some (name, rty)
      | _ -> None)
    items

type resu = Suc of built_in_ctx | Fai of string

let item_check bctx imp_m (name, rty) =
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
      Suc (rty_add_to_right bctx name #: rty)
  | None ->
      _task_fail name;
      Fai name

let struc_check bctx items =
  let bctx, imp_m = mk_imp_m bctx items in
  let tasks = mk_tasks items in
  let _, res =
    List.fold_left
      (fun (bctx, failed) item ->
        match item_check bctx imp_m item with
        | Suc bctx -> (bctx, failed)
        | Fai name -> (bctx, failed @ [ name ]))
      (bctx, []) tasks
  in
  let () = _log @@ fun _ -> Pp.printf "@{<bold>Summary:@}\n" in
  let () =
    match res with
    | [] ->
        _log @@ fun _ -> Pp.printf "@{<bold>@{<yellow>All tasks succeeded@}@}\n"
    | _ -> _log @@ fun _ -> List.iter _task_fail res
  in
  Some bctx
