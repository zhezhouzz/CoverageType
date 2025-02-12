open Language
open Zutils
open Subcty
(* open Myconfig *)

let rec sub_rty bctx rctx (rty1, rty2) =
  let rec aux rctx (rty1, rty2) =
    match (rty1, rty2) with
    | RtyBase { ou = Over; cty = cty1 }, RtyBase { ou = Over; cty = cty2 } ->
        sub_cty bctx rctx cty1 cty2
    | RtyBase { ou = Under; cty = cty1 }, RtyBase { ou = Under; cty = cty2 } ->
        sub_cty bctx rctx cty2 cty1
    | ( RtyArr
          {
            arr_type = GhostOverBaseArr;
            arg = arg1;
            argrty = argrty1;
            retty = retty1;
          },
        _ ) ->
        aux (Typectx.add_to_right rctx arg1 #: argrty1) (retty1, rty2)
    | ( _,
        RtyArr
          {
            arr_type = GhostOverBaseArr;
            arg = arg2;
            argrty = argrty2;
            retty = retty2;
          } ) ->
        aux (Typectx.add_to_right rctx arg2 #: argrty2) (rty1, retty2)
    | ( RtyArr
          { arr_type = NormalArr; arg = arg1; argrty = argrty1; retty = retty1 },
        RtyArr
          { arr_type = NormalArr; arg = arg2; argrty = argrty2; retty = retty2 }
      ) ->
        sub_rty bctx rctx (argrty2, argrty1)
        &&
        let retty2 =
          subst_rty_instance arg2 (AVar arg1 #: (erase_rty argrty1)) retty2
        in
        sub_rty bctx (Typectx.add_to_right rctx arg1 #: argrty2) (retty1, retty2)
    | _, _ ->
        _failatwith [%here]
          (spf "die: %s <: %s" (layout_rty rty1) (layout_rty rty2))
  in
  aux rctx (rty1, rty2)

let non_emptiness_rty builtin_ctx ctx rty =
  match rty with
  | RtyBase { ou = Under; cty } -> non_emptiness_cty builtin_ctx ctx cty
  | RtyArr { arr_type = NormalArr; _ } -> true
  | _ -> _failatwith [%here] "die"
