open Core
open Language
open Zutils

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let print_source_code source_file () =
  let code = Preprocess.preproress source_file in
  let _ = Pp.printf "%s\n" (layout_structure code) in
  ()

let subtype_check source_file () =
  let code = Preprocess.preproress source_file in
  let _, rty1 = get_rty_by_name code "rty1" in
  let _, rty2 = get_rty_by_name code "rty2" in
  let ctx = Typectx.emp in
  let _ =
    pprint_subtyping
      (fun () -> Typectx.pprint_ctx layout_rty Typectx.emp)
      (rty1, rty2) ()
  in
  let res =
    Auxtyping.sub_rty (Preprocess.load_bctx ()) Typectx.emp (rty1, rty2)
  in
  Pp.printf "@{<bold>result: %b:@}\n" res

let type_check source_file () =
  let code = Preprocess.preproress source_file in
  (* let () = Pp.printf "@{<bold>result:@} %s\n" (layout_structure code) in *)
  (* let () = _die [%here] in *)
  let _ = Typing.struc_check (Preprocess.load_bctx ()) code in
  ()

let one_param_file message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        and source_file = anon ("source_code_file" %: regular_file) in
        let () = Myconfig.meta_config_path := config_file in
        f source_file)
  in
  (message, cmd)

let commands =
  Command.group ~summary:"Poirot"
    [
      one_param_file "print-source-code" print_source_code;
      one_param_file "subtype-check" subtype_check;
      one_param_file "type-check" type_check;
    ]

let () = Command_unix.run commands
