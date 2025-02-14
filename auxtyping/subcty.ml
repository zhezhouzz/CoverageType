open Language
open Zutils
open Prop
open Myconfig
open Zdatatype

let layout_qt = function Nt.Fa -> "∀" | Nt.Ex -> "∃"

let layout_qv { x = qt, x; ty } =
  spf "%s%s:{%s}" (layout_qt qt) x @@ layout_cty ty

let layout_vs qt uqvs =
  List.split_by_comma layout_qv
  @@ List.map (fun { x; ty } -> { x = (qt, x); ty }) uqvs

let layout_prop_ = layout_prop

let report_unclosed loc query =
  let fvs = fv_prop query in
  _assert loc
    (spf "the cty query has free variables %s"
       (List.split_by_comma
          (function { x; ty } -> spf "%s:%s" x (Nt.layout ty))
          fvs))
    (0 == List.length fvs)

let check_valid axioms query =
  let () =
    _log_debug @@ fun _ ->
    Printf.printf "check valid: %s\n" (layout_prop_ query)
  in
  let () = report_unclosed [%here] query in
  let _ = Prover.update_axioms axioms in
  Prover.check_valid query

let check_sat axioms query =
  let () =
    _log_debug @@ fun _ ->
    Printf.printf "check valid: %s\n" (layout_prop_ query)
  in
  let () = report_unclosed [%here] query in
  let _ = Prover.update_axioms axioms in
  Prover.check_sat_bool query

let sub_cty builtin_ctx ctx cty1 cty2 =
  let overctx, underctx = build_wf_ctx (Typectx.ctx_to_list ctx) in
  let () =
    _log_queries @@ fun _ ->
    let overctx =
      List.map (fun (x, cty) -> x #: (RtyBase { ou = Over; cty })) overctx
    in
    let underctx =
      List.map (fun (x, cty) -> x #: (RtyBase { ou = Under; cty })) underctx
    in
    let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
    Typectx.pprint_ctx layout_rty ctx'
  in
  let () =
    _assert [%here]
      "left-hand-side type should be closed under over + under ctx"
      (is_close_cty (List.map fst (overctx @ underctx)) cty1)
  in
  let () =
    _assert [%here] "right-hand-side type should be closed under over ctx"
      (is_close_cty (List.map fst overctx) cty2)
  in
  let nty = Nt._type_unify [%here] cty1.nty cty2.nty in
  let overctx = (default_v, mk_top_cty nty) :: overctx in
  let query =
    List.fold_right
      (fun (x, { nty; phi }) query ->
        smart_forall [ x #: nty ] (smart_implies phi query))
      overctx
    @@ List.fold_right
         (fun (x, { nty; phi }) query ->
           smart_exists [ x #: nty ] (smart_add_to phi query))
         underctx
    @@ smart_implies cty1.phi cty2.phi
  in
  let () =
    _log_queries @@ fun _ ->
    Printf.printf "check valid: %s\n" (layout_prop_ query)
  in
  check_valid (bctx_to_axioms builtin_ctx) query

let non_emptiness_cty builtin_ctx ctx cty =
  let overctx, underctx = build_wf_ctx (Typectx.ctx_to_list ctx) in
  let () =
    _log_queries @@ fun _ ->
    let overctx =
      List.map (fun (x, cty) -> x #: (RtyBase { ou = Over; cty })) overctx
    in
    let underctx =
      List.map (fun (x, cty) -> x #: (RtyBase { ou = Under; cty })) underctx
    in
    let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
    Typectx.pprint_ctx layout_rty ctx'
  in
  let () =
    _assert [%here]
      "left-hand-side type should be closed under over + under ctx"
      (is_close_cty (List.map fst (overctx @ underctx)) cty)
  in
  let underctx = underctx @ [ (default_v, mk_top_cty cty.nty) ] in
  let query =
    List.fold_right
      (fun (x, { nty; phi }) query ->
        smart_forall [ x #: nty ] (smart_implies phi query))
      overctx
    @@ List.fold_right
         (fun (x, { nty; phi }) query ->
           smart_exists [ x #: nty ] (smart_add_to phi query))
         underctx
    @@ cty.phi
  in
  let () =
    _log_queries @@ fun _ ->
    Printf.printf "check sat: %s\n" (layout_prop_ query)
  in
  check_sat (bctx_to_axioms builtin_ctx) query
