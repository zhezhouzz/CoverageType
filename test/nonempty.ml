open Auxtyping
open Typing
open Language
open Zutils

let check_rty basic_ctx rty =
  check_wf_rty rty;
  let _ = Preprocess.rty_type_check basic_ctx [] rty in
  ()

let construct_basic_ctx rctx =
  let basic_ctx = Preprocess.load_basic_ctx () in
  let rctx_list = Typectx.ctx_to_list rctx.rty_ctx in
  List.fold_left
    (fun acc { x; ty = rty } ->
      check_wf_rty rty;
      let _ = Preprocess.rty_type_check acc [] rty in
      match rty with
      | RtyBase { cty = { nty; _ }; _ } -> Typectx.add_to_right acc x#:nty
      | _ -> acc)
    basic_ctx rctx_list

let rec mk_long_arr = function
  | [] ->
      _die_with [%here] "cannot construct arrow type from empty list of types"
  | [ ty ] -> ty
  | ty :: rest -> Nt.mk_arr ty (mk_long_arr rest)

let is_nonempty_rty name rctx rty =
  Statistic.clear ();
  Statistic.create_ignored_stat name;
  let root = Sys.getenv "DUNE_SOURCEROOT" in
  Sys.chdir root;
  Myconfig.meta_config_path := "test/meta-config.json";
  let basic_ctx = construct_basic_ctx rctx in
  check_rty basic_ctx rty;
  non_emptiness_rty rctx rty

let%test "[v: int | true]" =
  let test_name = "test" in
  let rctx = Rctx.emp test_name [] [] in
  let cty = { nty = Nt.int_ty; phi = Prop.mk_true } in
  let rty = RtyBase { ou = Under; cty } in
  is_nonempty_rty test_name rctx rty

let%test "[v: int | false]" =
  let test_name = "test" in
  let rctx = Rctx.emp test_name [] [] in
  let cty = { nty = Nt.int_ty; phi = Prop.mk_false } in
  let rty = RtyBase { ou = Under; cty } in
  not @@ is_nonempty_rty test_name rctx rty

let%test "[v:bool | v == (size == 0)]" =
  let open Nt in
  let test_name = "test" in
  let rctx = Rctx.emp test_name [] [] in
  let size_rty =
    let v_int = (AVar default_v#:int_ty)#:int_ty in
    let int_int_bool_ty = mk_long_arr [ int_ty; int_ty; bool_ty ] in
    let geq_func = ">="#:int_int_bool_ty in
    let zero = (AC (I 0))#:int_ty in
    let phi = Lit (AAppOp (geq_func, [ v_int; zero ]))#:bool_ty in
    RtyBase { ou = Over; cty = { nty = int_ty; phi } }
  in
  let goal_rty =
    let v_bool = (AVar default_v#:bool_ty)#:bool_ty in
    let size = (AVar "size"#:int_ty)#:int_ty in
    let int_int_bool_ty = mk_long_arr [ int_ty; int_ty; bool_ty ] in
    let bool_bool_bool_ty = mk_long_arr [ bool_ty; bool_ty; bool_ty ] in
    let eq_int = "=="#:int_int_bool_ty in
    let eq_bool = "=="#:bool_bool_bool_ty in
    let zero = (AC (I 0))#:int_ty in
    let inner_eq = (AAppOp (eq_int, [ size; zero ]))#:bool_ty in
    let phi = Lit (AAppOp (eq_bool, [ v_bool; inner_eq ]))#:bool_ty in
    RtyBase { ou = Under; cty = { nty = bool_ty; phi } }
  in
  let rctx = Rctx.add_var rctx "size"#:size_rty in
  is_nonempty_rty test_name rctx goal_rty
