open Zutils
open OcamlParser
open Mutils
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar

let rec axiom_to_expr (axiom : Nt.t prop) =
  match axiom with
  | 
   | Lit lit -> (layout_typed_lit lit, true)
    | Implies (p1, p2) ->
        (spf "%s %s %s" (p_layout p1) sym_implies (p_layout p2), false)
    | And [ p ] -> layout p
    | Or [ p ] -> layout p
    | And [ p1; p2 ] -> (spf "%s%s%s" (p_layout p1) sym_and (p_layout p2), false)
    | Or [ p1; p2 ] -> (spf "%s%s%s" (p_layout p1) sym_or (p_layout p2), false)
    | And ps -> (spf "%s" @@ List.split_by sym_and p_layout ps, false)
    | Or ps -> (spf "%s" @@ List.split_by sym_or p_layout ps, false)
    | Not p -> (spf "%s%s" sym_not (p_layout p), true)
    | Iff (p1, p2) -> (spf "%s %s %s" (p_layout p1) sym_iff (p_layout p2), false)
    | Ite (p1, p2, p3) ->
        ( spf "if %s then %s else %s"
            (fst @@ layout p1)
            (fst @@ layout p2)
            (fst @@ layout p3),
          false )
    | Forall { qv; body } ->
        (spf "%s%s, %s" sym_forall (layout_typedid qv) (p_layout body), false)
    | Exists { qv; body } ->
        (spf "%s%s, %s" sym_exists (layout_typedid qv) (p_layout body), false)


  | Forall {qv; }
  | Err -> mk_construct ("Err", [])
  | Tuple es ->
      desc_to_ocamlexpr @@ Pexp_tuple (List.map typed_axiom_to_expr es)
  | Var var -> typed_to_expr mkvar var
  | Const v -> constant_to_expr v
  | Let { if_rec; lhs; rhs; letbody } ->
      let flag = if if_rec then Asttypes.Recursive else Asttypes.Nonrecursive in
      let vb = mk_vb (typed_ids_to_pattern lhs, typed_axiom_to_expr rhs) in
      desc_to_ocamlexpr @@ Pexp_let (flag, [ vb ], typed_axiom_to_expr letbody)
  | AppOp (op, args) ->
      (* NOTE: to make the printed code looks clearer, we don't print type of operators. *)
      mk_op_apply (layout_op op.x, List.map typed_axiom_to_expr args)
  | App (func, args) ->
      (* NOTE: to make the printed code looks clearer, we don't print type of function in its application. *)
      let func = axiom_to_expr func.x in
      let args =
        List.map (fun x -> (Asttypes.Nolabel, typed_axiom_to_expr x)) args
      in
      desc_to_ocamlexpr @@ Pexp_apply (func, args)
  | Ifte (e1, e2, e3) ->
      let e1, e2, e3 = map3 typed_axiom_to_expr (e1, e2, e3) in
      desc_to_ocamlexpr @@ Pexp_ifthenelse (e1, e2, Some e3)
  | Match { matched; match_cases } ->
      desc_to_ocamlexpr
      @@ Pexp_match
           (typed_axiom_to_expr matched, List.map match_case_to_expr match_cases)
  | Lam { lamarg; lambody } ->
      mklam (typed_id_to_pattern lamarg) (typed_axiom_to_expr lambody)
