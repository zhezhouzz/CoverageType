open Language
open Zutils
open Sugar
open Typectx
open Auxtyping

let _log = Myconfig._log_typing

module Rctx = struct
  type rctx = { gctx : Nt.t rty ctx; ctx : Nt.t rty ctx }

  let emp = { gctx = emp; ctx = emp }
  let to_ctx { gctx; ctx } = concat gctx ctx
  let add_gvar rctx x = { rctx with gctx = add_to_right rctx.gctx x }

  let add_var { gctx; ctx } x =
    let gvars, rty = destruct_grty x.ty in
    let gctx = add_to_rights gctx gvars in
    let ctx = add_to_right ctx x.x #: rty in
    let x = x.x #: rty in
    ({ gctx; ctx }, x)

  let add_base_vars = List.fold_left (fun ctx x -> fst @@ add_var ctx x)

  let diff_exists_rty_opt ctx1 ctx2 rty =
    let* gvars = subtract_opt (equal_rty Nt.equal_nt) ctx1.gctx ctx2.gctx in
    let* vars = subtract_opt (equal_rty Nt.equal_nt) ctx1.ctx ctx2.ctx in
    let _ =
      _log @@ fun () ->
      Pp.printf "exists [%s], [%s] into %s\n" (layout_rtyed_vars gvars)
        (layout_rtyed_vars vars) (layout_rty rty)
    in
    Some (construct_grty gvars @@ exists_rtys vars rty)

  let diff_exists_rty loc ctx1 ctx2 rty =
    match diff_exists_rty_opt ctx1 ctx2 rty with
    | None -> _die loc
    | Some rty -> rty

  let pprint { gctx; ctx } () =
    Typectx.pprint_ctx layout_rty gctx;
    print_newline ();
    Typectx.pprint_ctx layout_rty ctx;
    print_newline ()
end

open Rctx

let _warinning_subtyping_error loc (rty1, rty2) =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s <: %s\n" (pos_to_string loc)
    (layout_rty rty1) (layout_rty rty2)

let _warinning_nonemptiness_error loc rty1 =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s is empty type\n" (pos_to_string loc)
    (layout_rty rty1)

let _warinning_typing_error loc (str, rty) =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s : %s\n" (pos_to_string loc) str
    (layout_rty rty)

let pprint_typing_check_term rctx (e, ty) =
  _log @@ pprint_typing_check (pprint rctx) (layout_typed_term e, layout_rty ty)

let pprint_typing_infer_term_before rctx e =
  _log @@ pprint_typing_infer (pprint rctx) (layout_typed_term e, "??")

let layout_rty_opt res =
  match res with Some res -> layout_rty res | None -> "None"

let pprint_typing_infer_term_after rctx (e, ty) =
  _log
  @@ pprint_typing_infer (pprint rctx) (layout_typed_term e, layout_rty_opt ty)

let pprint_typing_check_value rctx (e, ty) =
  _log @@ pprint_typing_check (pprint rctx) (layout_typed_value e, layout_rty ty)

let pprint_typing_infer_value_before rctx e =
  _log @@ pprint_typing_infer (pprint rctx) (layout_typed_value e, "??")

let pprint_typing_infer_value_after rctx (e, ty) =
  _log
  @@ pprint_typing_infer (pprint rctx) (layout_typed_value e, layout_rty_opt ty)

let rec lookup_ctxs ctxs id =
  match ctxs with
  | [] -> None
  | ctx :: ctxs -> (
      match get_opt ctx id with
      | Some res -> Some res
      | None -> lookup_ctxs ctxs id)

(** Debug *)
