open ParseTree
open Zutils

let rec subst_value (string_x : string) f (value_e : 't value) =
  match value_e with
  | VConst constant0 -> VConst constant0
  | VVar _t_stringtyped0 ->
      if String.equal _t_stringtyped0.x string_x then f _t_stringtyped0
      else VVar _t_stringtyped0
  | VLam { lamarg; body } ->
      if String.equal lamarg.x string_x then VLam { lamarg; body }
      else VLam { lamarg; body = typed_subst_term string_x f body }
  | VFix { fixname; fixarg; body } ->
      if String.equal fixname.x string_x then VFix { fixname; fixarg; body }
      else if String.equal fixarg.x string_x then VFix { fixname; fixarg; body }
      else VFix { fixname; fixarg; body = typed_subst_term string_x f body }
  | VTu _t__tvaluetypedlist0 ->
      VTu (List.map (typed_subst_value string_x f) _t__tvaluetypedlist0)

and typed_subst_value (string_x : string) f (value_e : ('t, 't value) typed) =
  value_e #-> (subst_value string_x f)

and subst_term (string_x : string) f (term_e : 't term) =
  match term_e with
  | CErr -> CErr
  | CVal _t__tvaluetyped0 ->
      CVal (typed_subst_value string_x f _t__tvaluetyped0)
  | CLetE { rhs; lhs; body } ->
      if String.equal lhs.x string_x then
        CLetE { rhs = typed_subst_term string_x f rhs; lhs; body }
      else
        CLetE
          {
            rhs = typed_subst_term string_x f rhs;
            lhs;
            body = typed_subst_term string_x f body;
          }
  | CLetDeTu { turhs; tulhs; body } ->
      if List.exists (fun x -> String.equal string_x x.x) tulhs then
        CLetDeTu { turhs = typed_subst_value string_x f turhs; tulhs; body }
      else
        CLetDeTu
          {
            turhs = typed_subst_value string_x f turhs;
            tulhs;
            body = typed_subst_term string_x f body;
          }
  | CApp { appf; apparg } ->
      CApp
        {
          appf = typed_subst_value string_x f appf;
          apparg = typed_subst_value string_x f apparg;
        }
  | CAppOp { op; appopargs } ->
      CAppOp
        { op; appopargs = List.map (typed_subst_value string_x f) appopargs }
  | CMatch { matched; match_cases } ->
      CMatch
        {
          matched = typed_subst_value string_x f matched;
          match_cases = List.map (subst_match_case string_x f) match_cases;
        }

and typed_subst_term (string_x : string) f (term_e : ('t, 't term) typed) =
  term_e #-> (subst_term string_x f)

and subst_match_case (string_x : string) f (match_case_e : 't match_case) =
  match match_case_e with
  | CMatchcase { constructor; args; exp } ->
      if List.exists (fun x -> String.equal string_x x.x) args then
        CMatchcase { constructor; args; exp }
      else
        CMatchcase { constructor; args; exp = typed_subst_term string_x f exp }

and typed_subst_match_case (string_x : string) f
    (match_case_e : ('t, 't match_case) typed) =
  match_case_e #-> (subst_match_case string_x f)

let rec subst_raw_term (string_x : string) f (raw_term_e : 't raw_term) =
  match raw_term_e with
  | Var _t_stringtyped0 ->
      if String.equal _t_stringtyped0.x string_x then f _t_stringtyped0
      else Var _t_stringtyped0
  | Const constant0 -> Const constant0
  | Lam { lamarg; lambody } ->
      if String.equal lamarg.x string_x then Lam { lamarg; lambody }
      else Lam { lamarg; lambody = typed_subst_raw_term string_x f lambody }
  | Err -> Err
  | Let { if_rec; rhs; lhs; letbody } ->
      if List.exists (fun x -> String.equal string_x x.x) lhs then
        Let { if_rec; rhs = typed_subst_raw_term string_x f rhs; lhs; letbody }
      else
        Let
          {
            if_rec;
            rhs = typed_subst_raw_term string_x f rhs;
            lhs;
            letbody = typed_subst_raw_term string_x f letbody;
          }
  | App (_t__traw_termtyped0, _t__traw_termtypedlist1) ->
      App
        ( typed_subst_raw_term string_x f _t__traw_termtyped0,
          List.map (typed_subst_raw_term string_x f) _t__traw_termtypedlist1 )
  | AppOp (_t_optyped0, _t__traw_termtypedlist1) ->
      AppOp
        ( _t_optyped0,
          List.map (typed_subst_raw_term string_x f) _t__traw_termtypedlist1 )
  | Ite (_t__traw_termtyped0, _t__traw_termtyped1, _t__traw_termtyped2) ->
      Ite
        ( typed_subst_raw_term string_x f _t__traw_termtyped0,
          typed_subst_raw_term string_x f _t__traw_termtyped1,
          typed_subst_raw_term string_x f _t__traw_termtyped2 )
  | Tu _t__traw_termtypedlist0 ->
      Tu (List.map (typed_subst_raw_term string_x f) _t__traw_termtypedlist0)
  | Match { matched; match_cases } ->
      Match
        {
          matched = typed_subst_raw_term string_x f matched;
          match_cases = List.map (subst_raw_match_case string_x f) match_cases;
        }

and typed_subst_raw_term (string_x : string) f
    (raw_term_e : ('t, 't raw_term) typed) =
  raw_term_e #-> (subst_raw_term string_x f)

and subst_raw_match_case (string_x : string) f
    (raw_match_case_e : 't raw_match_case) =
  match raw_match_case_e with
  | Matchcase { constructor; args; exp } ->
      if List.exists (fun x -> String.equal string_x x.x) args then
        Matchcase { constructor; args; exp }
      else
        Matchcase
          { constructor; args; exp = typed_subst_raw_term string_x f exp }

and typed_subst_raw_match_case (string_x : string) f
    (raw_match_case_e : ('t, 't raw_match_case) typed) =
  raw_match_case_e #-> (subst_raw_match_case string_x f)

open Prop

let rec subst_cty (string_x : string) f (cty_e : 't cty) =
  match cty_e with { nty; phi } -> { nty; phi = subst_prop string_x f phi }

and typed_subst_cty (string_x : string) f (cty_e : ('t, 't cty) typed) =
  cty_e #-> (subst_cty string_x f)

let rec subst_rty (string_x : string) f (rty_e : 't rty) =
  match rty_e with
  | RtyBase { ou; cty } -> RtyBase { ou; cty = subst_cty string_x f cty }
  | RtyArr { arr_type; argrty; arg; retty } ->
      let argrty = subst_rty string_x f argrty in
      if String.equal arg string_x then RtyArr { arr_type; argrty; arg; retty }
      else RtyArr { arr_type; argrty; arg; retty = subst_rty string_x f retty }
  | RtyProd (r1, r2) ->
      RtyProd (subst_rty string_x f r1, subst_rty string_x f r2)

and typed_subst_rty (string_x : string) f (rty_e : ('t, 't rty) typed) =
  rty_e #-> (subst_rty string_x f)
