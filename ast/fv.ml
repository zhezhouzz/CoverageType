open ParseTree
open Zutils

let rec fv_value (value_e : 't value) =
  match value_e with
  | VConst _ -> []
  | VVar _t_stringtyped0 -> [] @ [ _t_stringtyped0 ]
  | VLam { lamarg; body } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_term body)
        [ lamarg ]
  | VFix { fixname; fixarg; body } ->
      Zdatatype.List.substract (typed_eq String.equal)
        (Zdatatype.List.substract (typed_eq String.equal)
           ([] @ typed_fv_term body)
           [ fixarg ])
        [ fixname ]
  | VTu _t__tvaluetypedlist0 ->
      [] @ List.concat (List.map typed_fv_value _t__tvaluetypedlist0)

and typed_fv_value (value_e : ('t, 't value) typed) = fv_value value_e.x

and fv_term (term_e : 't term) =
  match term_e with
  | CErr -> []
  | CVal _t__tvaluetyped0 -> [] @ typed_fv_value _t__tvaluetyped0
  | CLetE { rhs; lhs; body } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_term body)
        [ lhs ]
      @ typed_fv_term rhs
  | CLetDeTu { turhs; tulhs; body } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_term body)
        tulhs
      @ typed_fv_value turhs
  | CApp { appf; apparg } -> ([] @ typed_fv_value apparg) @ typed_fv_value appf
  | CAppOp { appopargs; _ } ->
      [] @ List.concat (List.map typed_fv_value appopargs)
  | CMatch { matched; match_cases } ->
      (List.concat @@ List.map fv_match_case match_cases)
      @ typed_fv_value matched

and typed_fv_term (term_e : ('t, 't term) typed) = fv_term term_e.x

and fv_match_case (match_case_e : 't match_case) =
  match match_case_e with
  | CMatchcase { args; exp; _ } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_term exp)
        args

and typed_fv_match_case (match_case_e : ('t, 't match_case) typed) =
  fv_match_case match_case_e.x

let rec fv_raw_term (raw_term_e : 't raw_term) =
  match raw_term_e with
  | Var _t_stringtyped0 -> [] @ [ _t_stringtyped0 ]
  | Const _ -> []
  | Lam { lamarg; lambody } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_raw_term lambody)
        [ lamarg ]
  | Err -> []
  | Let { rhs; lhs; letbody; _ } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_raw_term letbody)
        lhs
      @ typed_fv_raw_term rhs
  | App (_t__traw_termtyped0, _t__traw_termtypedlist1) ->
      ([] @ List.concat (List.map typed_fv_raw_term _t__traw_termtypedlist1))
      @ typed_fv_raw_term _t__traw_termtyped0
  | AppOp (_, _t__traw_termtypedlist1) ->
      [] @ List.concat (List.map typed_fv_raw_term _t__traw_termtypedlist1)
  | Ite (_t__traw_termtyped0, _t__traw_termtyped1, _t__traw_termtyped2) ->
      (([] @ typed_fv_raw_term _t__traw_termtyped2)
      @ typed_fv_raw_term _t__traw_termtyped1)
      @ typed_fv_raw_term _t__traw_termtyped0
  | Tu _t__traw_termtypedlist0 ->
      [] @ List.concat (List.map typed_fv_raw_term _t__traw_termtypedlist0)
  | Match { matched; match_cases } ->
      ([] @ List.concat (List.map fv_raw_match_case match_cases))
      @ typed_fv_raw_term matched

and typed_fv_raw_term (raw_term_e : ('t, 't raw_term) typed) =
  fv_raw_term raw_term_e.x

and fv_raw_match_case (raw_match_case_e : 't raw_match_case) =
  match raw_match_case_e with
  | Matchcase { args; exp; _ } ->
      Zdatatype.List.substract (typed_eq String.equal)
        ([] @ typed_fv_raw_term exp)
        args

and typed_fv_raw_match_case (raw_match_case_e : ('t, 't raw_match_case) typed) =
  fv_raw_match_case raw_match_case_e.x

open Prop

let rec fv_cty (cty_e : 't cty) =
  match cty_e with
  | { phi; _ } ->
      let res = [] @ fv_prop phi in
      List.filter_map
        (fun x -> if String.equal default_v x.x then None else Some x)
        res

and typed_fv_cty (cty_e : ('t, 't cty) typed) = fv_cty cty_e.x

let rec fv_rty (rty_e : 't rty) =
  match rty_e with
  | RtyBase { cty; _ } -> [] @ fv_cty cty
  | RtyArr { argrty; arg; retty; _ } ->
      let res = [] @ fv_rty retty in
      let res =
        List.filter_map
          (fun x -> if String.equal arg x.x then None else Some x)
          res
      in
      res @ fv_rty argrty
  | RtyProd (r1, r2) -> [] @ List.concat (List.map fv_rty [ r1; r2 ])

and typed_fv_rty (rty_e : ('t, 't rty) typed) = fv_rty rty_e.x

let rec fv_item (item_e : 't item) =
  match item_e with
  | MTyDecl _ -> []
  | MValDecl _ -> []
  | MMethodPred _ -> []
  | MAxiom { prop; _ } -> [] @ fv_prop prop
  | MFuncImpRaw { body; _ } -> [] @ typed_fv_raw_term body
  | MFuncImp { body; _ } -> [] @ typed_fv_term body
  | MRty { rty; _ } -> [] @ fv_rty rty

and typed_fv_item (item_e : ('t, 't item) typed) = fv_item item_e.x
