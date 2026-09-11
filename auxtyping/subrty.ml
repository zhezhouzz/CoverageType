open Language
open Zutils
open Subcty
(* open Myconfig *)

let rec sub_rty rctx (rty1, rty2) =
  ( TypecheckerLog.typing @@ fun _ ->
    pprint_subtyping
      (fun () ->
        Typectx.pprint_ctx layout_rty rctx.rty_ctx;
        print_newline ())
      (rty1, rty2) () );
  let aux rctx (rty1, rty2) =
    match (rty1, rty2) with
    | RtyBase { ou = Over; cty = cty1 }, RtyBase { ou = Over; cty = cty2 } ->
        if equal_cty (fun _ _ -> true) cty1 cty2 then true
        else sub_cty Over rctx cty1 cty2
    | RtyBase { ou = Under; cty = cty1 }, RtyBase { ou = Under; cty = cty2 } ->
        if equal_cty (fun _ _ -> true) cty1 cty2 then true
        else sub_cty Under rctx cty1 cty2
    | ( RtyArr { arg = arg1; argrty = argrty1; retty = retty1 },
        RtyArr { arg = arg2; argrty = argrty2; retty = retty2 } ) ->
        sub_rty rctx (argrty2, argrty1)
        &&
        let retty2 =
          subst_rty_instance arg2 (AVar arg1#:(erase_rty argrty1)) retty2
        in
        sub_rty
          {
            rctx with
            rty_ctx = Typectx.add_to_right rctx.rty_ctx arg1#:argrty2;
          }
          (retty1, retty2)
    | _, _ ->
        _failatwith [%here]
          (spf "die: %s <: %s" (layout_rty rty1) (layout_rty rty2))
  in
  let () = Statistic.stat_count_query rctx.task_name in
  aux rctx (rty1, rty2)

let non_emptiness_rty rctx rty =
  let () = Statistic.stat_count_query rctx.task_name in
  match rty with
  | RtyBase { ou = Under; cty } -> non_emptiness_cty rctx cty
  | RtyArr _ -> true
  | RtyPolyPred _ -> true
  | _ -> _failatwith [%here] "die"
