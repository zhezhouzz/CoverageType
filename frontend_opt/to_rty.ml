open Zutils
open OcamlParser
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar
open To_cty

let rec layout_rty = function
  | RtyBase { ou; cty } -> (
      match ou with
      | Over -> spf "{%s}" (layout_cty cty)
      | Under -> spf "[%s]" (layout_cty cty))
  | RtyArr { arr_type; argrty; arg; retty } ->
      let argrty = layout_rty_bracket argrty in
      let arr =
        match arr_type with NormalArr -> "→" | GhostOverBaseArr -> "⇢"
      in
      if List.exists (String.equal arg) @@ fv_rty_id retty then
        spf "%s:%s %s %s" arg argrty arr (layout_rty retty)
      else spf "%s %s %s" argrty arr (layout_rty retty)
  | RtyProd (r1, r2) ->
      spf "%s × %s" (layout_rty_bracket r1) (layout_rty_bracket r2)

and layout_rty_bracket rty =
  match rty with
  | RtyBase _ -> layout_rty rty
  | _ -> spf "(%s)" (layout_rty rty)

let get_ou expr =
  match expr.pexp_attributes with
  | l when List.exists (fun x -> String.equal x.attr_name.txt "over") l -> Over
  | _ -> Under

let get_arr_type expr =
  match expr.pexp_attributes with
  | l when List.exists (fun x -> String.equal x.attr_name.txt "ghost") l ->
      GhostOverBaseArr
  | _ -> NormalArr

let rec rty_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> RtyBase { ou = get_ou expr; cty = cty_of_expr expr }
  | Pexp_fun (_, Some rtyexpr, pattern, body) ->
      let retty = rty_of_expr body in
      let arg = id_of_pattern pattern in
      let arr_type = get_arr_type rtyexpr in
      let argrty = rty_of_expr rtyexpr in
      RtyArr { arr_type; argrty; arg; retty }
  (* | Pexp_let (_, [ vb ], body) -> ( *)
  (*     let retty = rty_of_expr body in *)
  (*     let arg = id_of_pattern vb.pvb_pat in *)
  (*     match rty_of_expr vb.pvb_expr with *)
  (*     | RtyBase { cty; _ } -> RtyBaseArr { argcty = cty; arg; retty } *)
  (*     | RtyTuple _ -> _die [%here] *)
  (*     | argrty -> RtyArrArr { argrty; retty }) *)
  | Pexp_tuple es -> mk_rty_tuple (List.map rty_of_expr es)
  | _ ->
      _failatwith [%here]
        (spf "wrong refinement type: %s" (Pprintast.string_of_expression expr))

let rty_of_expr expr =
  let rty = rty_of_expr expr in
  check_wf_rty rty;
  rty
