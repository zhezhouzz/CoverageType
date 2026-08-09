open Zutils
open OcamlParser
open Oparse
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar
open To_cty

let rec layout_rty = function
  | RtyBase { ou; cty } -> layout_ou_bracket ou @@ layout_cty cty
  | RtyArr { argrty; arg; retty } ->
      let argrty = layout_rty_bracket argrty in
      let arr = "→" in
      if List.exists (String.equal arg) @@ fv_rty_id retty then
        spf "%s:%s %s %s" arg argrty arr (layout_rty retty)
      else spf "%s %s %s" argrty arr (layout_rty retty)
  | RtyPolyType { pt; rty } ->
      spf "%s%s.%s" (Nt.qt_pretty_layout Fa) pt (layout_rty rty)
  | RtyPolyPred { pred; rty } ->
      spf "%s(%s: %s).%s" (Nt.qt_pretty_layout Fa) pred.x (Nt.layout_nt pred.ty)
        (layout_rty rty)

and layout_rty_bracket rty =
  match rty with
  | RtyBase _ -> layout_rty rty
  | _ -> spf "(%s)" (layout_rty rty)

let get_ou expr =
  match expr.pexp_attributes with
  | l when List.exists (fun x -> String.equal x.attr_name.txt "over") l -> Over
  | _ -> Under

let base_type_name = Nt._constructor_ty_0 "baseType"
let _monad = "M"

let rec rty_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> RtyBase { ou = get_ou expr; cty = cty_of_expr expr }
  | Pexp_fun (Asttypes.Nolabel, None, pattern, body) ->
      let param = To_raw_term.typed_id_of_pattern pattern in
      if Nt.equal_nt base_type_name param.ty then
        RtyPolyType { pt = param.x; rty = rty_of_expr body }
      else RtyPolyPred { pred = param; rty = rty_of_expr body }
  | Pexp_fun (Asttypes.Optional _, None, pattern, body) ->
      let param = To_raw_term.typed_id_of_pattern pattern in
      let retty = rty_of_expr body in
      let argrty = mk_top_overrty param.ty in
      RtyArr { argrty; arg = param.x; retty }
  | Pexp_fun (_, Some rtyexpr, pattern, body) ->
      let retty = rty_of_expr body in
      let arg = id_of_pattern pattern in
      (* let arr_type = get_arr_type rtyexpr in *)
      let argrty = rty_of_expr rtyexpr in
      RtyArr { argrty; arg; retty }
  | Pexp_let (_, [ vb ], body) ->
      let retty = rty_of_expr body in
      let arg = id_of_pattern vb.pvb_pat in
      (* let arr_type = get_arr_type vb.pvb_expr in *)
      let argrty = rty_of_expr vb.pvb_expr in
      RtyArr { argrty; arg; retty }
  | Pexp_construct (c, Some expr) when String.equal _monad (longid_to_id c) ->
      mk_return_rty (rty_of_expr expr)
  | _ ->
      _failatwith [%here]
        (spf "wrong refinement type: %s" (string_of_expression expr))

let rty_of_expr expr =
  let rty = rty_of_expr expr in
  check_syntactically_wf_rty rty;
  rty
