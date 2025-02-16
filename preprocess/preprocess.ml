include Basic_typing
include Normalization
open Language
open Zutils

let parse file =
  ocaml_structure_to_items
  @@ OcamlParser.Pparse.parse_implementation ~tool_name:"ocamlc" file

let _ctxs = ref None
let _log = Myconfig._log_preprocess

let predefined_files =
  [ "basic_typing.ml"; "refinement_typing.ml"; "axioms.ml" ]

let load_ctxs () =
  match !_ctxs with
  | Some ctxs -> ctxs
  | None ->
      let prim_path = Myconfig.get_prim_path () in
      let items =
        List.concat_map
          (fun file -> parse (spf "%s/%s" prim_path.predefined_path file))
          predefined_files
      in
      let basic_ctx, items = struct_check Typectx.emp items in
      let builtin_ctx = struct_mk_rty_ctx items in
      let axioms = struct_mk_axiom_ctx items in
      let bctx = { builtin_ctx; axioms } in
      let res = (basic_ctx, bctx) in
      _ctxs := Some res;
      res

let load_basic_ctx () = fst @@ load_ctxs ()
let load_bctx () = snd @@ load_ctxs ()

let preproress source_file =
  let _, code = struct_check (load_basic_ctx ()) @@ parse source_file in
  normalize_structure code
