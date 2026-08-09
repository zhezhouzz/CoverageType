open ParseTree
open Zutils
open Fv
open Subst
open Map
open Zdatatype

let fv_value_id e = fv_typed_id_to_id fv_value e
let typed_fv_value_id e = fv_typed_id_to_id typed_fv_value e
let fv_term_id e = fv_typed_id_to_id fv_term e
let typed_fv_term_id e = fv_typed_id_to_id typed_fv_term e
let fv_match_case_id e = fv_typed_id_to_id fv_match_case e
let typed_fv_match_case_id e = fv_typed_id_to_id typed_fv_match_case e

let subst_value_instance x instance e =
  subst_f_to_instance subst_value x instance e

let typed_subst_value_instance x instance e =
  subst_f_to_instance typed_subst_value x instance e

let subst_term_instance x instance e =
  subst_f_to_instance subst_term x instance e

let typed_subst_term_instance x instance e =
  subst_f_to_instance typed_subst_term x instance e

let subst_match_case_instance x instance e =
  subst_f_to_instance subst_match_case x instance e

let typed_subst_match_case_instance x instance e =
  subst_f_to_instance typed_subst_match_case x instance e

let fv_raw_term_id e = fv_typed_id_to_id fv_raw_term e
let typed_fv_raw_term_id e = fv_typed_id_to_id typed_fv_raw_term e
let fv_raw_match_case_id e = fv_typed_id_to_id fv_raw_match_case e
let typed_fv_raw_match_case_id e = fv_typed_id_to_id typed_fv_raw_match_case e

let subst_raw_term_instance x instance e =
  subst_f_to_instance subst_raw_term x instance e

let typed_subst_raw_term_instance x instance e =
  subst_f_to_instance typed_subst_raw_term x instance e

let subst_raw_match_case_instance x instance e =
  subst_f_to_instance subst_raw_match_case x instance e

let typed_subst_raw_match_case_instance x instance e =
  subst_f_to_instance typed_subst_raw_match_case x instance e

let fv_cty_id e = fv_typed_id_to_id fv_cty e
let typed_fv_cty_id e = fv_typed_id_to_id typed_fv_cty e
let subst_cty_instance x instance e = subst_f_to_instance subst_cty x instance e

let typed_subst_cty_instance x instance e =
  subst_f_to_instance typed_subst_cty x instance e

let fv_rty_id e = fv_typed_id_to_id fv_rty e
let typed_fv_rty_id e = fv_typed_id_to_id typed_fv_rty e
let subst_rty_instance x instance e = subst_f_to_instance subst_rty x instance e

let typed_subst_rty_instance x instance e =
  subst_f_to_instance typed_subst_rty x instance e

let fv_item_id e = fv_typed_id_to_id fv_item e
let typed_fv_item_id e = fv_typed_id_to_id typed_fv_item e
let term_to_opt_term e = map_term (fun x -> Some x) e
let typed_term_to_opt_typed_term e = typed_map_term (fun x -> Some x) e
let value_to_opt_value e = map_value (fun x -> Some x) e
let typed_value_to_opt_typed_value e = typed_map_value (fun x -> Some x) e

open Sugar

(** Well-fromed Rty *)

(** Aux functions *)

let is_free_cty x rty = List.exists (String.equal x) @@ fv_cty_id rty

let is_close_cty dom rty =
  (* let open Zdatatype in *)
  (* let () = *)
  (*   Printf.printf "fvs: %s; dom: %s\n" *)
  (*     (StrList.to_string (fv_cty_id rty)) *)
  (*     (StrList.to_string dom) *)
  (* in *)
  List.for_all (fun x -> List.exists (String.equal x) dom) @@ fv_cty_id rty

let is_free_rty x rty = List.exists (String.equal x) @@ fv_rty_id rty

let is_close_rty dom rty =
  List.for_all (fun x -> List.exists (String.equal x) dom) @@ fv_rty_id rty

let rec check_syntactically_wf_rty = function
  | RtyBase _ -> ()
  | RtyArr { argrty; arg; retty } -> (
      match argrty with
      | RtyBase { ou = Over; _ } -> check_syntactically_wf_rty retty
      | RtyArr _ as funcrty ->
          _assert [%here]
            "rty not well-formed: function arg cannot be free in return type"
            (not (is_free_rty arg retty));
          check_syntactically_wf_rty funcrty;
          check_syntactically_wf_rty retty
      | _ ->
          _die_with [%here]
            "rty not well-formed: function arg must be over or arrow type")
  | RtyPolyType { rty; _ } -> check_syntactically_wf_rty rty
  | RtyPolyPred { rty; _ } -> check_syntactically_wf_rty rty

let constant_to_value c = (VConst c)#:(Prop.constant_to_nt c)
let value_to_term v = (CVal v)#:v.ty
let term_to_value e = match e.x with CVal v -> v.x#:e.ty | _ -> _die [%here]
let id_to_value v = (VVar v)#:v.ty
let id_to_term v = value_to_term @@ id_to_value v

let map_rty_retty f rty =
  let rec aux rty =
    match rty with
    | RtyBase { ou; cty } -> RtyBase { ou; cty = f cty }
    | RtyArr { argrty; arg; retty } -> RtyArr { argrty; arg; retty = aux retty }
    | RtyPolyType { pt; rty } -> RtyPolyType { pt; rty = aux rty }
    | RtyPolyPred { pred; rty } -> RtyPolyPred { pred; rty = aux rty }
  in
  aux rty

let mk_lam lamarg body = (VLam { lamarg; body })#:(Nt.mk_arr lamarg.ty body.ty)

let mk_id_function ty =
  let lamarg = "x"#:ty in
  (VLam { lamarg; body = id_to_term lamarg })#:(Nt.mk_arr ty ty)

let mk_fix fixname fixarg body = (VFix { fixname; fixarg; body })#:fixname.ty

let lam_to_fix fixname body =
  match body.x with
  | VLam { lamarg; body } -> mk_fix fixname lamarg body
  | _ -> _die [%here]

let lam_to_fix_comp fixname body =
  value_to_term (lam_to_fix fixname (term_to_value body))

let mk_lete lhs rhs body = (CLetE { lhs; rhs; body })#:body.ty
let mk_app appf apparg = (CApp { appf; apparg })#:(Nt.get_arr_rhs appf.ty)

let mk_appop op appopargs =
  let paratys, retty = Nt.destruct_arr_tp op.ty in
  let paratys =
    List.sublist paratys ~start_included:(List.length appopargs)
      ~end_excluded:(List.length paratys)
  in
  let retty = Nt.construct_arr_tp (paratys, retty) in
  (CAppOp { op; appopargs })#:retty

let rec __get_lam_term_ty loc = function
  | Lam { lamarg; lambody } -> (
      let t1 =
        match lamarg.ty with
        | Nt.Ty_unknown -> _failatwith loc "__get_lam_term_ty"
        | _ -> lamarg.ty
      in
      match lambody.ty with
      | Nt.Ty_unknown -> Nt.mk_arr t1 (__get_lam_term_ty loc lambody.x)
      | _ -> Nt.mk_arr t1 lambody.ty)
  | _ -> _failatwith loc "__get_lam_term_ty"

let rec lift_poly_rty = function
  | RtyPolyType { pt; rty } ->
      let pts, rty = lift_poly_rty rty in
      (pts @ [ pt ], rty)
  | _ as rty -> ([], rty)

let rec lift_poly_pred_rty = function
  | RtyPolyType _ -> _die [%here]
  | RtyPolyPred { pred; rty } ->
      let pds, rty = lift_poly_pred_rty rty in
      (pds @ [ pred ], rty)
  | _ as rty -> ([], rty)

let gather_poly_preds_rty =
  let rec aux = function
    | RtyBase { cty; _ } -> Prop.gather_poly_preds_from_prop cty.phi
    | RtyArr { argrty; retty; _ } -> aux argrty @ aux retty
    | RtyPolyType { rty; _ } -> aux rty
    | RtyPolyPred { pred; rty } ->
        List.filter (fun p -> not (String.equal p.x pred.x)) @@ aux rty
  in
  aux

let construct_poly_rty (pts, rty) =
  List.fold_right (fun pt rty -> RtyPolyType { pt; rty }) pts rty

let construct_poly_pred_rty (pds, rty) =
  List.fold_right (fun pred rty -> RtyPolyPred { pred; rty }) pds rty

let rec construct_rty (args, rty) =
  match args with
  | [] -> rty
  | x :: args ->
      RtyArr { arg = x.x; argrty = x.ty; retty = construct_rty (args, rty) }

let remove_redundant_poly_pred rty =
  let pts, rty = lift_poly_rty rty in
  let preds, rty = lift_poly_pred_rty rty in
  let fpreds = gather_poly_preds_rty rty in
  let preds =
    List.filter
      (fun p -> List.exists (fun p' -> String.equal p.x p'.x) fpreds)
      preds
  in
  construct_poly_rty (pts, construct_poly_pred_rty (preds, rty))

let erase_cty = function { nty; _ } -> nty

let rec erase_rty = function
  | RtyBase { cty; _ } -> erase_cty cty
  | RtyArr { argrty; retty; _ } ->
      Nt.mk_arr (erase_rty argrty) (erase_rty retty)
  | RtyPolyType { pt; rty } -> Nt.Ty_poly (pt, erase_rty rty)
  | RtyPolyPred { rty; _ } -> erase_rty rty

let rec get_ou_rty = function
  | RtyBase { ou; _ } -> Some ou
  | RtyPolyType { rty; _ } -> get_ou_rty rty
  | RtyPolyPred { rty; _ } -> get_ou_rty rty
  | RtyArr _ -> None

let is_base_rty rty = match get_ou_rty rty with Some _ -> true | _ -> false

let is_over_base_rty rty =
  match get_ou_rty rty with Some Over -> true | _ -> false

let is_under_base_rty rty =
  match get_ou_rty rty with Some Under -> true | _ -> false

let destruct_base_rty = function
  | RtyBase { ou; cty } -> (ou, cty)
  | _ -> failwith "assume_base_rty"

let destruct_arr_rty loc = function
  | RtyArr { argrty; arg; retty } -> (argrty, arg, retty)
  | _ -> _die loc

let is_over_arr_rty = function
  | RtyArr { argrty = RtyBase { ou = Over; _ }; arg; retty } -> true
  | _ -> false

let is_under_arr_rty = function
  | RtyArr { argrty = RtyBase { ou = Under; _ }; arg; retty } -> true
  | _ -> false

let is_arr_arr_rty = function
  | RtyArr { argrty = RtyArr _; arg; retty } -> true
  | _ -> false

let ou_to_qt = function Over -> Nt.Fa | Under -> Nt.Ex
let qt_to_ou = function Nt.Fa -> Over | Nt.Ex -> Under

let get_rty_by_name (item_e : 't item list) (x : string) =
  let res =
    List.filter_map
      (function
        | MRty { is_assumption; name; rty } when String.equal name x ->
            Some (is_assumption, rty)
        | _ -> None)
      item_e
  in
  match res with [] -> _die [%here] | [ x ] -> x | _ -> _die [%here]

let mk_top_cty nty = { nty; phi = Prop.mk_true }
let mk_bot_cty nty = { nty; phi = Prop.mk_false }
let cty_to_overrty cty = RtyBase { ou = Over; cty }
let cty_to_underrty cty = RtyBase { ou = Under; cty }

let mk_top_overrty nty =
  if Nt.is_base_tp nty then cty_to_overrty @@ mk_top_cty nty else _die [%here]

let mk_bot_overrty nty =
  if Nt.is_base_tp nty then cty_to_overrty @@ mk_bot_cty nty else _die [%here]

let rec mk_top_underrty nty =
  match nty with
  | Nt.Ty_arrow (t1, t2) ->
      let argrty = mk_top_overrty t1 in
      let retty = mk_top_underrty t2 in
      RtyArr { arg = Rename.dummy_var (); argrty; retty }
  | _ -> cty_to_underrty @@ mk_top_cty nty

let rec mk_bot_underrty nty =
  match nty with
  | Nt.Ty_arrow (t1, t2) ->
      let argrty = mk_top_overrty t1 in
      let retty = mk_bot_underrty t2 in
      RtyArr { arg = Rename.dummy_var (); argrty; retty }
  | _ -> cty_to_underrty @@ mk_bot_cty nty

let mk_unit_underrty phi =
  RtyBase { ou = Under; cty = { nty = Nt.unit_ty; phi } }

open Prop

let rec value_to_lit loc = function
  | VVar x -> AVar x
  | VConst c -> AC c
  | VTuple vs ->
      let lits = List.map (fun x -> lit_to_tlit @@ value_to_lit loc x.x) vs in
      ATu lits
  | _ -> _die loc

let mk_eq_lit_prop lit =
  lit_to_prop @@ mk_lit_eq_lit [%here] (AVar default_v#:lit.ty) lit.x

let mk_eq_var_prop x = lit_to_prop (mk_var_eq_var [%here] default_v#:x.ty x)

let mk_eq_c_prop c =
  lit_to_prop (mk_var_eq_c [%here] default_v#:(constant_to_nt c) c)

let mk_eq_lit_cty x = { nty = x.ty; phi = mk_eq_lit_prop x }
let mk_eq_tvar_cty x = { nty = x.ty; phi = mk_eq_var_prop x }
let mk_eq_c_cty c = { nty = constant_to_nt c; phi = mk_eq_c_prop c }
let mk_eq_tvar_overrty x = RtyBase { ou = Over; cty = mk_eq_tvar_cty x }
let mk_eq_tvar_underrty x = RtyBase { ou = Under; cty = mk_eq_tvar_cty x }
let mk_eq_c_overrty x = RtyBase { ou = Over; cty = mk_eq_c_cty x }
let mk_eq_c_underrty x = RtyBase { ou = Under; cty = mk_eq_c_cty x }
let mk_eq_lit_underrty x = RtyBase { ou = Under; cty = mk_eq_lit_cty x }

let as_under_base_rty loc = function
  | RtyBase { ou = Under; cty } -> cty
  | _ -> _die loc

let flip_rty rty =
  match rty with
  | RtyBase { ou = Over; cty } -> RtyBase { ou = Under; cty }
  | RtyBase { ou = Under; cty } -> RtyBase { ou = Over; cty }
  | _ -> rty

(** Denormalize *)

let rec typed_value_to_typed_raw_term (value_e : ('t, 't value) typed) =
  match value_e.x with
  | VConst constant0 -> (Const constant0)#:value_e.ty
  | VVar _t_stringtyped0 -> (Var _t_stringtyped0)#:value_e.ty
  | VLam { lamarg; body } ->
      (Lam { lamarg; lambody = typed_term_to_typed_raw_term body })#:value_e.ty
  | VFix { fixarg; body; _ } ->
      (* let tmp = (VLam { lamarg = fixarg; body }) #: body.ty in *)
      let tmp = (VLam { lamarg = fixarg; body })#:value_e.ty in
      typed_value_to_typed_raw_term tmp
  | VTuple _t__tvaluetypedlist0 ->
      (Tuple (List.map typed_value_to_typed_raw_term _t__tvaluetypedlist0))#:value_e
                                                                               .ty

and typed_term_to_typed_raw_term (term_e : ('t, 't term) typed) =
  match term_e.x with
  | CErr -> Err#:term_e.ty
  | CVal _t__tvaluetyped0 -> typed_value_to_typed_raw_term _t__tvaluetyped0
  | CRecord l ->
      let e =
        Record (List.map (fun (x, v) -> (x, typed_value_to_typed_raw_term v)) l)
      in
      e#:term_e.ty
  | CField { rd; field } ->
      let e = Field (typed_value_to_typed_raw_term rd, field) in
      e#:term_e.ty
  | CLetE { rhs; lhs; body } ->
      (Let
         {
           rhs = typed_term_to_typed_raw_term rhs;
           lhs = [ lhs ];
           letbody = typed_term_to_typed_raw_term body;
           if_rec = false;
         })#:term_e.ty
  | CLetDeTuple { turhs; tulhs; body } ->
      (Let
         {
           rhs = typed_value_to_typed_raw_term turhs;
           lhs = tulhs;
           letbody = typed_term_to_typed_raw_term body;
           if_rec = false;
         })#:term_e.ty
  | CApp { appf; apparg } ->
      (App
         ( typed_value_to_typed_raw_term appf,
           [ typed_value_to_typed_raw_term apparg ] ))#:term_e.ty
  | CAppOp { op; appopargs } ->
      (AppOp (op, List.map typed_value_to_typed_raw_term appopargs))#:term_e.ty
  | CMatch { matched; match_cases } ->
      (Match
         {
           matched = typed_value_to_typed_raw_term matched;
           match_cases = List.map macth_case_to_raw_macth_case match_cases;
         })#:term_e.ty

and macth_case_to_raw_macth_case = function
  | CMatchcase { constructor; args; exp } ->
      Matchcase { constructor; args; exp = typed_term_to_typed_raw_term exp }

let denormalize_term = typed_term_to_typed_raw_term
let denormalize_value = typed_value_to_typed_raw_term

let denormalize_item (item : Nt.t item) =
  match item with
  | MFuncImp { name; if_rec; body } ->
      let body = denormalize_term body in
      MFuncImpRaw { name; if_rec; body }
  | _ -> item

let denormalize_structure = List.map denormalize_item

(* Typectx *)

open Typectx

let rty_add_to_right { builtin_ctx; cur_axiom_names } x =
  { builtin_ctx = add_to_right builtin_ctx x; cur_axiom_names }

let axiom_add_to_right { builtin_ctx; cur_axiom_names } (x, tasks, prop) =
  if List.exists (String.equal x) cur_axiom_names then _die [%here]
  else
    let () = Prop.Prover.update_axioms [ (x, tasks, prop) ] in
    { builtin_ctx; cur_axiom_names = cur_axiom_names @ [ x ] }

let rty_add_to_rights { builtin_ctx; cur_axiom_names } x =
  { builtin_ctx = add_to_rights builtin_ctx x; cur_axiom_names }

let axiom_add_to_rights { builtin_ctx; cur_axiom_names } xs =
  if
    List.exists
      (fun (x, _, _) -> List.exists (String.equal x) cur_axiom_names)
      xs
  then _die [%here]
  else
    let () = Prop.Prover.update_axioms xs in
    {
      builtin_ctx;
      cur_axiom_names = cur_axiom_names @ List.map (fun (x, _, _) -> x) xs;
    }

(** Monad *)

let mk_return_rty retty =
  RtyArr
    { retty; arg = Rename.dummy_var (); argrty = mk_top_overrty Nt.unit_ty }

let ret_ty loc = function RtyArr { retty; _ } -> retty | _ -> _die loc

let mk_nfv_arr argrty retty =
  RtyArr { argrty; retty; arg = Rename.dummy_var () }

let get_raw_function_name x = match x.x with Var x -> Some x.x | _ -> None

let is_raw_monadic_bind x =
  match get_raw_function_name x with
  | Some x when String.equal x _bind -> true
  | _ -> false

let is_raw_monadic_fmap x =
  match get_raw_function_name x with
  | Some x when String.equal x _fmap -> true
  | _ -> false

let get_op_name x = match x.x with PrimOp x -> Some x | _ -> None

let is_monadic_bind x =
  match get_op_name x with
  | Some x when String.equal x _bind -> true
  | _ -> false

let is_monadic_fmap x =
  match get_op_name x with
  | Some x when String.equal x _fmap -> true
  | _ -> false

let rec fresh_name_rty rty =
  match rty with
  | RtyBase { ou; cty = { nty; phi } } ->
      RtyBase { ou; cty = { nty; phi = fresh_name_prop phi } }
  | RtyArr { argrty; arg; retty } ->
      let argrty = fresh_name_rty argrty in
      let arg' = Rename.unique_var arg in
      let retty =
        subst_rty_instance arg (AVar arg'#:(erase_rty argrty)) retty
      in
      RtyArr { argrty; arg = arg'; retty = fresh_name_rty retty }
  | RtyPolyType { pt; rty } ->
      let pt' = Rename.unique_type_var pt in
      let rty = map_rty (Nt.subst_nt (pt, Nt.Ty_var pt')) rty in
      RtyPolyType { pt = pt'; rty = fresh_name_rty rty }
  | RtyPolyPred { pred; rty } ->
      let pred' = pred#->Rename.unique_var in
      let rty = rename_pred_rty pred.x pred'.x rty in
      RtyPolyPred { pred = pred'; rty = fresh_name_rty rty }

(** Poly *)

let rename_pred_cty oldname newname { nty; phi } =
  { nty; phi = rename_pred_prop oldname newname phi }

let rec rename_pred_rty oldname newname rty =
  match rty with
  | RtyBase { ou; cty } ->
      RtyBase { ou; cty = rename_pred_cty oldname newname cty }
  | RtyArr { argrty; arg; retty } ->
      let argrty = rename_pred_rty oldname newname argrty in
      let retty = rename_pred_rty oldname newname retty in
      RtyArr { argrty; arg; retty }
  | RtyPolyType { pt; rty } ->
      RtyPolyType { pt; rty = rename_pred_rty oldname newname rty }
  | RtyPolyPred { pred; rty } ->
      if String.equal oldname pred.x then RtyPolyPred { pred; rty }
      else RtyPolyPred { pred; rty = rename_pred_rty oldname newname rty }

let raw_term_to_list (to_elem : ('t, 't raw_term) typed -> 'a) =
  let rec aux e =
    match e.x with
    | AppOp (op, args) -> (
        match (op.x, args) with
        | DtConstructor "[]", [] -> []
        | DtConstructor "::", [ hd; tl ] -> to_elem hd :: aux tl
        | _ -> _die [%here])
    | _ -> _die [%here]
  in
  aux

let raw_term_to_tuple (to_elem : ('t, 't raw_term) typed -> 'a) e =
  match e.x with Tuple l -> List.map to_elem l | _ -> _die [%here]

let raw_term_to_str_list e =
  raw_term_to_list
    (fun e -> match e.x with Var x -> x.x | _ -> _die [%here])
    e

let mk_capture captured_ts captured_preds captured_vars =
  { captured_ts; captured_preds; captured_vars }

(* stat *)

let rec counter_branch_value (value_e : 't value) =
  match value_e with
  | VConst _ | VVar _ -> 0
  | VLam { body; _ } -> counter_branch_term body.x
  | VFix { body; _ } -> counter_branch_term body.x
  | VTuple vs ->
      List.fold_left (fun res x -> res + counter_branch_value x.x) 0 vs

and counter_branch_term (term_e : 't term) : int =
  match term_e with
  | CErr | CRecord _ | CField _ -> 0
  | CVal v -> counter_branch_value v.x
  | CLetE { rhs; body; _ } ->
      counter_branch_term rhs.x + counter_branch_term body.x
  | CLetDeTuple { turhs; body; _ } ->
      counter_branch_value turhs.x + counter_branch_term body.x
  | CApp { appf; apparg } ->
      counter_branch_value appf.x + counter_branch_value apparg.x
  | CAppOp { op; appopargs } ->
      List.fold_left (fun res x -> res + counter_branch_value x.x) 0 appopargs
  | CMatch { matched; match_cases } ->
      let new_adding = List.length match_cases - 1 in
      List.fold_left
        (fun res -> function
          | CMatchcase { exp; _ } -> res + counter_branch_term exp.x)
        new_adding match_cases

let counter_branch_from_term e = 1 + counter_branch_term e.x
let counter_branch_from_value e = 1 + counter_branch_value e.x

let rec counter_lvar_value (value_e : 't value) =
  match value_e with
  | VConst _ | VVar _ -> 0
  | VLam { body; _ } -> 1 + counter_lvar_term body.x
  | VFix { body; _ } -> 2 + counter_lvar_term body.x
  | VTuple vs -> List.fold_left (fun res x -> res + counter_lvar_value x.x) 0 vs

and counter_lvar_term (term_e : 't term) : int =
  match term_e with
  | CErr | CRecord _ | CField _ -> 0
  | CVal v -> counter_lvar_value v.x
  | CLetE { rhs; body; _ } ->
      1 + counter_lvar_term rhs.x + counter_lvar_term body.x
  | CLetDeTuple { turhs; tulhs; body } ->
      List.length tulhs + counter_lvar_value turhs.x + counter_lvar_term body.x
  | CApp { appf; apparg } ->
      counter_lvar_value appf.x + counter_lvar_value apparg.x
  | CAppOp { op; appopargs } ->
      List.fold_left (fun res x -> res + counter_lvar_value x.x) 0 appopargs
  | CMatch { matched; match_cases } ->
      List.fold_left
        (fun res -> function
          | CMatchcase { exp; _ } -> res + counter_lvar_term exp.x)
        0 match_cases

let if_rec_value = function VFix _ -> true | _ -> false
let if_rec_term = function CVal v -> if_rec_value v.x | _ -> false

let counter_rty_qt_qpred (rty : Nt.t rty) : int * int =
  let rec aux (qt, qpred) = function
    | RtyPolyType { rty; _ } -> aux (1 + qt, qpred) rty
    | RtyPolyPred { rty; _ } -> aux (qt, 1 + qpred) rty
    | _ -> (qt, qpred)
  in
  aux (0, 0) rty
