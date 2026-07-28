open Auxtyping
open Typing
open Language

let is_nonempty_rty name rctx rty =
  Statistic.clear ();
  Statistic.create_ignored_stat name;
  let root = Sys.getenv "DUNE_SOURCEROOT" in
  Sys.chdir root;
  Myconfig.meta_config_path := "test/meta-config.json";
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
