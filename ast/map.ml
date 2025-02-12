open ParseTree
open Zutils

let rec map_value (f : 't -> 's) (value_e : 't value) =
  match value_e with
  | VConst constant0 -> VConst constant0
  | VVar _t_stringtyped0 -> VVar _t_stringtyped0 #=> f
  | VLam { lamarg; body } ->
      VLam { lamarg = lamarg #=> f; body = typed_map_term f body }
  | VFix { fixname; fixarg; body } ->
      VFix
        {
          fixname = fixname #=> f;
          fixarg = fixarg #=> f;
          body = typed_map_term f body;
        }
  | VTu _t__tvaluetypedlist0 ->
      VTu (List.map (typed_map_value f) _t__tvaluetypedlist0)

and typed_map_value (f : 't -> 's) (value_e : ('t, 't value) typed) =
  value_e #=> f #-> (map_value f)

and map_term : 't 's. ('t -> 's) -> 't term -> 's term =
 fun f term_e ->
  match term_e with
  | CErr -> CErr
  | CVal _t__tvaluetyped0 -> CVal (typed_map_value f _t__tvaluetyped0)
  | CLetE { rhs; lhs; body } ->
      CLetE
        {
          rhs = typed_map_term f rhs;
          lhs = lhs #=> f;
          body = typed_map_term f body;
        }
  | CLetDeTu { turhs; tulhs; body } ->
      CLetDeTu
        {
          turhs = typed_map_value f turhs;
          tulhs = List.map (fun x -> x #=> f) tulhs;
          body = typed_map_term f body;
        }
  | CApp { appf; apparg } ->
      CApp { appf = typed_map_value f appf; apparg = typed_map_value f apparg }
  | CAppOp { op; appopargs } ->
      CAppOp
        { op = op #=> f; appopargs = List.map (typed_map_value f) appopargs }
  | CMatch { matched; match_cases } ->
      CMatch
        {
          matched = typed_map_value f matched;
          match_cases = List.map (map_match_case f) match_cases;
        }

and typed_map_term :
      't 's. ('t -> 's) -> ('t, 't term) typed -> ('s, 's term) typed =
 fun f term_e -> term_e #=> f #-> (map_term f)

and map_match_case : 't 's. ('t -> 's) -> 't match_case -> 's match_case =
 fun f match_case_e ->
  match match_case_e with
  | CMatchcase { constructor; args; exp } ->
      CMatchcase
        {
          constructor = constructor #=> f;
          args = List.map (fun x -> x #=> f) args;
          exp = typed_map_term f exp;
        }

let rec map_raw_term : 't 's. ('t -> 's) -> 't raw_term -> 's raw_term =
 fun f raw_term_e ->
  match raw_term_e with
  | Var _t_stringtyped0 -> Var _t_stringtyped0 #=> f
  | Const constant0 -> Const constant0
  | Lam { lamarg; lambody } ->
      Lam { lamarg = lamarg #=> f; lambody = typed_map_raw_term f lambody }
  | Err -> Err
  | Let { if_rec; rhs; lhs; letbody } ->
      Let
        {
          if_rec;
          rhs = typed_map_raw_term f rhs;
          lhs = List.map (fun x -> x #=> f) lhs;
          letbody = typed_map_raw_term f letbody;
        }
  | App (_t__traw_termtyped0, _t__traw_termtypedlist1) ->
      App
        ( typed_map_raw_term f _t__traw_termtyped0,
          List.map (typed_map_raw_term f) _t__traw_termtypedlist1 )
  | AppOp (_t_optyped0, _t__traw_termtypedlist1) ->
      AppOp
        ( _t_optyped0 #=> f,
          List.map (typed_map_raw_term f) _t__traw_termtypedlist1 )
  | Ite (_t__traw_termtyped0, _t__traw_termtyped1, _t__traw_termtyped2) ->
      Ite
        ( typed_map_raw_term f _t__traw_termtyped0,
          typed_map_raw_term f _t__traw_termtyped1,
          typed_map_raw_term f _t__traw_termtyped2 )
  | Tu _t__traw_termtypedlist0 ->
      Tu (List.map (typed_map_raw_term f) _t__traw_termtypedlist0)
  | Match { matched; match_cases } ->
      Match
        {
          matched = typed_map_raw_term f matched;
          match_cases = List.map (map_raw_match_case f) match_cases;
        }

and typed_map_raw_term :
      't 's. ('t -> 's) -> ('t, 't raw_term) typed -> ('s, 's raw_term) typed =
 fun (f : 't -> 's) (raw_term_e : ('t, 't raw_term) typed) ->
  raw_term_e #=> f #-> (map_raw_term f)

and map_raw_match_case (f : 't -> 's) (raw_match_case_e : 't raw_match_case) =
  match raw_match_case_e with
  | Matchcase { constructor; args; exp } ->
      Matchcase
        {
          constructor = constructor #=> f;
          args = List.map (fun x -> x #=> f) args;
          exp = typed_map_raw_term f exp;
        }

and typed_map_raw_match_case (f : 't -> 's)
    (raw_match_case_e : ('t, 't raw_match_case) typed) =
  raw_match_case_e #-> (map_raw_match_case f)

open Prop

let rec map_cty (f : 't -> 's) (cty_e : 't cty) =
  match cty_e with { nty; phi } -> { nty; phi = map_prop f phi }

and typed_map_cty (f : 't -> 's) (cty_e : ('t, 't cty) typed) =
  cty_e #=> f #-> (map_cty f)

let rec map_rty (f : 't -> 's) (rty_e : 't rty) =
  match rty_e with
  | RtyBase { ou; cty } -> RtyBase { ou; cty = map_cty f cty }
  | RtyArr { arr_type; argrty; arg; retty } ->
      RtyArr
        { arr_type; argrty = map_rty f argrty; arg; retty = map_rty f retty }
  | RtyProd (r1, r2) -> RtyProd (map_rty f r1, map_rty f r2)

and typed_map_rty (f : 't -> 's) (rty_e : ('t, 't rty) typed) =
  rty_e #=> f #-> (map_rty f)

let rec map_item (f : 't -> 's) (item_e : 't item) =
  match item_e with
  | MTyDecl { type_name; type_params; type_decls } ->
      MTyDecl { type_name; type_params; type_decls }
  | MValDecl _t_stringtyped0 -> MValDecl _t_stringtyped0 #=> f
  | MMethodPred _t_stringtyped0 -> MMethodPred _t_stringtyped0 #=> f
  | MAxiom { name; prop } -> MAxiom { name; prop = map_prop f prop }
  | MFuncImpRaw { name; if_rec; body } ->
      MFuncImpRaw
        { name = name #=> f; if_rec; body = typed_map_raw_term f body }
  | MFuncImp { name; if_rec; body } ->
      MFuncImp { name = name #=> f; if_rec; body = typed_map_term f body }
  | MRty { is_assumption; name; rty } ->
      MRty { is_assumption; name; rty = map_rty f rty }

and typed_map_item (f : 't -> 's) (item_e : ('t, 't item) typed) =
  item_e #=> f #-> (map_item f)
