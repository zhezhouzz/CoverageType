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

let smart_dependent_forall (x, { nty; phi }) query =
  let phi = subst_prop_instance default_v (AVar x#:nty) phi in
  smart_forall [ x#:nty ] (smart_implies phi query)

let smart_dependent_exists (x, { nty; phi }) query =
  let phi = subst_prop_instance default_v (AVar x#:nty) phi in
  smart_exists [ x#:nty ] (smart_add_to phi query)

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

let sub_cty ou builtin_ctx ctx cty1 cty2 =
  let overctx, underctx = build_wf_ctx (Typectx.ctx_to_list ctx) in
  let () =
    _log_queries @@ fun _ ->
    let overctx =
      List.map (fun (x, cty) -> x#:(RtyBase { ou = Over; cty })) overctx
    in
    let underctx =
      List.map (fun (x, cty) -> x#:(RtyBase { ou = Under; cty })) underctx
    in
    let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
    Typectx.pprint_ctx layout_rty ctx';
    print_newline ()
  in
  let () =
    let dom = List.map fst (overctx @ underctx) in
    _assert [%here]
      (spf
         "left-hand-side type %s should be closed under over + under ctx: [ %s \
          ]"
         (layout_rty (RtyBase { ou; cty = cty1 }))
         (StrList.to_string dom))
      (is_close_cty dom cty1)
  in
  let () =
    let dom = List.map fst (overctx @ underctx) in
    _assert [%here]
      (spf
         "right-hand-side type %s should be closed under over + under ctx: [ \
          %s ]"
         (layout_rty (RtyBase { ou; cty = cty2 }))
         (StrList.to_string dom))
      (is_close_cty dom cty2)
  in
  let nty = Nt._type_unify [%here] cty1.nty cty2.nty in
  let overctx = (default_v, mk_top_cty nty) :: overctx in
  let query =
    match ou with
    | Over -> smart_implies cty1.phi cty2.phi
    | Under -> smart_implies cty2.phi cty1.phi
  in
  let query =
    List.fold_right smart_dependent_forall overctx
    @@ List.fold_right smart_dependent_exists underctx query
  in
  let () =
    _log_queries @@ fun _ ->
    Printf.printf "check valid: %s\n" (layout_prop query)
  in
  let () =
    _log_queries @@ fun _ ->
    Printf.printf "let[@axiom] %s\n" (layout_prop__raw query)
  in
  check_valid (bctx_to_axioms builtin_ctx) query

(* NOTE: after exists the constraints into the return type, the emptiness can be checked final stage;
   It may cause the more branch analysis.
*)
let lazy_emptiness_check = true

let non_emptiness_cty builtin_ctx ctx cty =
  if lazy_emptiness_check then true
  else
    let overctx, underctx = build_wf_ctx (Typectx.ctx_to_list ctx) in
    let underctx = underctx @ [ (default_v, mk_top_cty cty.nty) ] in
    let () =
      _log_queries @@ fun _ ->
      let overctx =
        List.map (fun (x, cty) -> x#:(RtyBase { ou = Over; cty })) overctx
      in
      let underctx =
        List.map (fun (x, cty) -> x#:(RtyBase { ou = Under; cty })) underctx
      in
      let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
      Typectx.pprint_ctx layout_rty ctx';
      print_newline ()
    in
    let () =
      _assert [%here]
        "left-hand-side type should be closed under over + under ctx"
        (is_close_cty (List.map fst (overctx @ underctx)) cty)
    in
    let overctx = (default_v, mk_top_cty cty.nty) :: overctx in
    let query =
      List.fold_right smart_dependent_exists overctx
      @@ List.fold_right smart_dependent_forall underctx
      @@ cty.phi
    in
    let () =
      _log_queries @@ fun _ ->
      Printf.printf "check sat: %s\n" (layout_prop_ query)
    in
    check_sat (bctx_to_axioms builtin_ctx) query
