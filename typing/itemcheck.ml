open Language
open Zutils
open Bidirect
open Zdatatype

let _task_info name rty =
  TypecheckerLog.result @@ fun _ ->
  Pp.printf "@{<bold>Type Check %s:@}\n" name;
  Pp.printf "@{<bold>check against with:@} %s\n" (layout_rty rty)

let _task_succ name =
  TypecheckerLog.result @@ fun _ ->
  Pp.printf "@{<bold>@{<yellow>Task %s, type check succeeded@}@}\n" name

let _task_fail name =
  TypecheckerLog.result @@ fun _ ->
  Pp.printf "@{<bold>@{<red>Task %s, type check failed@}@}\n" name

let mk_imp_m bctx items =
  List.fold_left
    (fun (bctx, imp_m) item ->
      match item with
      | MFuncImp { name; body; _ } -> (bctx, StrMap.add name.x body imp_m)
      | MRty { is_assumption = true; name; rty } ->
          (rty_add_to_right bctx name#:rty, imp_m)
      | _ -> (bctx, imp_m))
    (bctx, StrMap.empty) items

let mk_invs items =
  List.fold_left
    (fun m -> function
      | MLocalRty { host_name; name; rty; _ } ->
          StrMap.update host_name
            (function
              | None -> Some [ name#:rty ] | Some l -> Some ((name#:rty) :: l))
            m
      | _ -> m)
    StrMap.empty items

let mk_tasks items =
  List.filter_map
    (function
      | MRty { is_assumption = false; name; rty } -> Some (name, rty)
      | _ -> None)
    items

type resu = Suc of built_in_ctx | Fai of string

let item_check bctx inv_m imp_m (name, rty) =
  let imp =
    StrMap.find
      (spf "The source code of given refinement type '%s' is missing." name)
      imp_m name
  in
  let () =
    TypecheckerLog.result @@ fun _ ->
    Pp.printf "@{<bold>imp_m(%s)@}\n%s\n" name (layout_typed_term imp)
  in
  let () = Statistic.create_stat name imp in
  let () = Statistic.stat_update_rty (name, counter_rty_qt_qpred rty) in
  let invs = match StrMap.find_opt inv_m name with None -> [] | Some l -> l in
  let sol, rty = instantiate_rty_by_nty [%here] rty imp.ty in
  let invs = List.map (fun x -> x#=>(map_rty (Nt.msubst_nt sol))) invs in
  let () = _task_info name rty in
  let time, res =
    clock (fun () ->
        term_type_check bctx (Common.Rctx.emp name [] invs) (imp, rty))
  in
  let () = Statistic.stat_total_time (name, time) in
  let () = Statistic.store_stat stat_file in
  match res with
  | Some _ ->
      _task_succ name;
      Suc (rty_add_to_right bctx name#:rty)
  | None ->
      _task_fail name;
      (* let () = _die [%here] in *)
      Fai name

let struc_check bctx items =
  let bctx, imp_m = mk_imp_m bctx items in
  let inv_m = mk_invs items in
  let tasks = mk_tasks items in
  let _, passed, failed =
    List.fold_left
      (fun (bctx, passed, failed) (name, rty) ->
        match item_check bctx inv_m imp_m (name, rty) with
        | Suc bctx -> (bctx, passed @ [ name ], failed)
        | Fai name -> (bctx, passed, failed @ [ name ]))
      (bctx, [], []) tasks
  in
  let () =
    TypecheckerLog.result @@ fun _ ->
    Pp.printf "@{<bold>Summary (total %i tasks):@}\n" (List.length tasks)
  in
  let () =
    match failed with
    | [] ->
        TypecheckerLog.result @@ fun _ ->
        Pp.printf "@{<bold>@{<yellow>All tasks succeeded@}@}\n"
    | _ -> TypecheckerLog.result @@ fun _ -> List.iter _task_fail failed
  in
  (Some bctx, passed, failed)
