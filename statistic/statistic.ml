open Sexplib.Std
open Language
open Zutils
open Zdatatype

type 'a ht_result = Value of 'a | Ignored | Missing

type stat = {
  function_name : string;
  branchs : int;
  if_rec : bool;
  lvar : int;
  num_qt : int;
  num_qpred : int;
  method_prdicates : string list;
  mp : int;
  query_times : float list;
  num_query : int;
  max_forall : int;
  max_exists : int;
  total_time : float;
  avg_time : float;
}
[@@deriving eq, ord, show, sexp, yojson]

type stat_list = stat list [@@deriving eq, ord, show, sexp, yojson]

let _stat_tab = Hashtbl.create 20

let find_stat name =
  match Hashtbl.find_opt _stat_tab name with
  | Some (Some stat) -> Value stat
  | Some None -> Ignored
  | None -> Missing

let insert_stat name stat =
  match find_stat name with
  | Missing -> Hashtbl.add _stat_tab name stat
  | _ -> _die_with [%here] (spf "creating duplicate stat %s" name)

let update_stat name f =
  match find_stat name with
  | Value stat -> Hashtbl.replace _stat_tab name (Some (f stat))
  | Ignored -> ()
  | Missing -> _die [%here]

let stat_update_rty (name, (num_qt, num_qpred)) =
  update_stat name (fun stat -> { stat with num_qt; num_qpred })

let stat_count_query name =
  update_stat name (fun stat -> { stat with num_query = stat.num_query + 1 })

let stat_query_time (name, time) =
  update_stat name (fun stat ->
      { stat with query_times = stat.query_times @ [ time ] })

let stat_query_formula (name, prop) =
  let preds = List.map _get_x @@ count_pred_prop prop in
  let num_fa, num_ex = count_prop_qv prop in
  update_stat name (fun stat ->
      let max_forall = max num_fa stat.max_forall in
      let max_exists = max num_ex stat.max_exists in
      let method_prdicates =
        List.slow_rm_dup String.equal (stat.method_prdicates @ preds)
      in
      { stat with max_forall; max_exists; method_prdicates })

let stat_total_time (name, total_time) =
  update_stat name (fun stat -> { stat with total_time })

let calculate_stat stat =
  (* let num_query = List.length stat.query_times in *)
  (* let query_time = List.fold_left ( +. ) 0.0 stat.query_times in *)
  let avg_time =
    if stat.num_query = 0 then 0.
    else stat.total_time /. float_of_int stat.num_query
  in
  let mp = List.length stat.method_prdicates in
  { stat with avg_time; mp }

let store_stat filename =
  let j =
    stat_list_to_yojson @@ List.map calculate_stat @@ List.of_seq
    @@ Seq.filter_map Fun.id
    @@ Hashtbl.to_seq_values _stat_tab
  in
  Yojson.Safe.to_file filename j

let create_stat function_name (imp : (Nt.t, Nt.t term) typed) =
  let branchs = counter_branch_from_term imp in
  let if_rec = if_rec_term imp.x in
  let lvar = counter_lvar_term imp.x in
  let mp = 0 in
  let stat =
    {
      function_name;
      branchs;
      if_rec;
      lvar;
      num_qt = 0;
      num_qpred = 0;
      method_prdicates = [];
      mp;
      query_times = [];
      num_query = 0;
      max_forall = 0;
      max_exists = 0;
      total_time = 0.0;
      avg_time = 0.0;
    }
  in
  insert_stat function_name (Some stat)

let create_subtyping_stat () =
  let function_name = "subtyping" in
  let mp = 0 in
  let stat =
    {
      function_name;
      branchs = 0;
      if_rec = false;
      lvar = 0;
      num_qt = 0;
      num_qpred = 0;
      method_prdicates = [];
      mp;
      query_times = [];
      num_query = 0;
      max_forall = 0;
      max_exists = 0;
      total_time = 0.0;
      avg_time = 0.0;
    }
  in
  insert_stat function_name (Some stat)

let create_ignored_stat name = insert_stat name None
let clear () = Hashtbl.clear _stat_tab
