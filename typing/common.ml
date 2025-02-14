open Language
open Zutils
open Sugar
open Typectx
open Auxtyping

let _log = Myconfig._log_typing

type rctx = { gctx : Nt.t rty ctx; ctx : Nt.t rty ctx }

let rctx_to_ctx { gctx; ctx } = concat gctx ctx
let rctx_add_gvar rctx x = { rctx with gctx = add_to_right rctx.gctx x }

let rctx_add_var { gctx; ctx } x =
  let gvars, rty = destruct_grty x.ty in
  let gctx = add_to_rights gctx gvars in
  let ctx = add_to_right ctx x.x #: rty in
  let x = x.x #: rty in
  ({ gctx; ctx }, x)

let rctx_diff_exists_rty_opt ctx1 ctx2 rty =
  let* gvars = subtract_opt (equal_rty Nt.equal_nt) ctx1.gctx ctx2.gctx in
  let* vars = subtract_opt (equal_rty Nt.equal_nt) ctx1.ctx ctx2.ctx in
  Some (construct_grty gvars @@ exists_rtys vars rty)

let rctx_diff_exists_rty loc ctx1 ctx2 rty =
  match rctx_diff_exists_rty_opt ctx1 ctx2 rty with
  | None -> _die loc
  | Some rty -> rty

let _warinning_subtyping_error loc (rty1, rty2) =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s <: %s\n" (pos_to_string loc)
    (layout_rty rty1) (layout_rty rty2)

let _warinning_subtyping_emptyness_error loc rty1 =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s is empty type\n" (pos_to_string loc)
    (layout_rty rty1)

let _warinning_typing_error loc (str, rty) =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s : %s\n" (pos_to_string loc) str
    (layout_rty rty)

let pprint_typing_check_term rctx (e, ty) =
  _log
  @@ pprint_typing_check
       (fun () ->
         Typectx.pprint_ctx layout_rty rctx.gctx;
         Typectx.pprint_ctx layout_rty rctx.ctx)
       (layout_typed_term e, layout_rty ty)

let pprint_typing_infer_term_before rctx e =
  _log
  @@ pprint_typing_infer
       (fun () ->
         Typectx.pprint_ctx layout_rty rctx.gctx;
         Typectx.pprint_ctx layout_rty rctx.ctx)
       (layout_typed_term e, "??")

let layout_rty_opt res =
  match res with Some res -> layout_rty res | None -> "None"

let pprint_typing_infer_term_after rctx (e, ty) =
  _log
  @@ pprint_typing_infer
       (fun () ->
         Typectx.pprint_ctx layout_rty rctx.gctx;
         Typectx.pprint_ctx layout_rty rctx.ctx)
       (layout_typed_term e, layout_rty_opt ty)

let pprint_typing_check_value rctx (e, ty) =
  _log
  @@ pprint_typing_check
       (fun () ->
         Typectx.pprint_ctx layout_rty rctx.gctx;
         Typectx.pprint_ctx layout_rty rctx.ctx)
       (layout_typed_value e, layout_rty ty)

let pprint_typing_infer_value_before rctx e =
  _log
  @@ pprint_typing_infer
       (fun () ->
         Typectx.pprint_ctx layout_rty rctx.gctx;
         Typectx.pprint_ctx layout_rty rctx.ctx)
       (layout_typed_value e, "??")

let pprint_typing_infer_value_after rctx (e, ty) =
  _log
  @@ pprint_typing_infer
       (fun () ->
         Typectx.pprint_ctx layout_rty rctx.gctx;
         Typectx.pprint_ctx layout_rty rctx.ctx)
       (layout_typed_value e, layout_rty_opt ty)

let rec lookup_ctxs ctxs id =
  match ctxs with
  | [] -> None
  | ctx :: ctxs -> (
      match get_opt ctx id with
      | Some res -> Some res
      | None -> lookup_ctxs ctxs id)
