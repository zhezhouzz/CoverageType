include Ast
include Prop
include Frontend_opt
open Zutils
open Zdatatype

let layout_rtyed_var { x; ty } = spf "%s:%s" x (layout_rty ty)
let layout_rtyed_vars l = List.split_by_comma layout_rtyed_var l

let rec is_wf_rty (over_ctx, under_ctx) = function
  | RtyBase { ou = Over; _ } as rty -> is_close_rty (List.map fst over_ctx) rty
  | RtyBase { ou = Under; _ } as rty ->
      is_close_rty (List.map fst over_ctx @ List.map fst under_ctx) rty
  | RtyProd (rty1, rty2) ->
      is_wf_rty (over_ctx, under_ctx) rty1
      && is_wf_rty (over_ctx, under_ctx) rty2
  | RtyArr { arg; argrty; retty; _ } ->
      is_wf_rty (over_ctx, under_ctx) argrty
      && is_wf_rty (wf_ctx_add (over_ctx, under_ctx) arg #: argrty) retty

and wf_ctx_add (over_ctx, under_ctx) { x; ty } =
  match ty with
  | RtyBase { ou = Over; cty } -> (over_ctx @ [ (x, cty) ], under_ctx)
  | RtyBase { ou = Under; cty } -> (over_ctx, under_ctx @ [ (x, cty) ])
  | RtyProd _ -> _die_with [%here] (spf "unimp prod type of %s" x)
  | RtyArr _ -> (over_ctx, under_ctx)

let build_wf_ctx (ctx : ('t rty, string) typed list) =
  List.fold_left wf_ctx_add ([], []) ctx
