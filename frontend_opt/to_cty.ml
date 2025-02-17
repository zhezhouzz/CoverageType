open Zutils
open OcamlParser
open Mutils
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar

let pprint_phi (phi : 't prop) =
  let res =
    let* lit = prop_force_typed_lit_opt phi in
    let* args = typed_lit_force_aappop_opt (lit, "==") in
    match args with
    | [ a; b ] ->
        let* v = typed_lit_force_avar_opt a in
        let* c = typed_lit_force_ac_opt b in
        if String.equal v.x default_v then Some c else None
    | _ -> None
  in
  match res with None -> layout_prop phi | Some c -> layout_constant c

let pprint = function
  | { nty; phi } ->
      if is_true phi then Nt.layout nty
      else if Nt.equal_nt Nt.unit_ty nty then layout_prop phi
      else spf "%s:%s | %s" default_v (Nt.layout nty) (layout_prop phi)

let layout_cty = pprint

let get_self ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Nt.core_type_to_t ty)
  | _ ->
      Printf.printf "\nct: %s\n" (layout_ct ct);
      _die [%here]

let vars_phi_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        (* let () = Printf.printf "\nct: %s\n" (layout_ct ct) in *)
        (* let () = *)
        (*   Printf.printf "\ne': %s\n" (Pprintast.string_of_expression e') *)
        (* in *)
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], prop_of_expr expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let cty_of_expr expr =
  match vars_phi_of_expr expr with
  | [ { x; ty } ], phi when String.equal x default_v -> { nty = ty; phi }
  | _ -> _failatwith [%here] (Pprintast.string_of_expression expr)
