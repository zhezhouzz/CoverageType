open ParseTree
open Zutils
open Fv
open Subst
open Map

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

(* Generated from _term.ml *)
open Sugar

let constant_to_value c = (VConst c) #: (Prop.constant_to_nt c)
let value_to_term v = (CVal v) #: v.ty
let term_to_value e = match e.x with CVal v -> v.x #: e.ty | _ -> _die [%here]
let id_to_value v = (VVar v) #: v.ty
let id_to_term v = value_to_term @@ id_to_value v

let mk_lam lamarg body =
  (VLam { lamarg; body }) #: (Nt.mk_arr lamarg.ty body.ty)

let mk_id_function ty =
  let lamarg = "x" #: ty in
  (VLam { lamarg; body = id_to_term lamarg }) #: (Nt.mk_arr ty ty)

let mk_fix fixname fixarg body = (VFix { fixname; fixarg; body }) #: fixname.ty

let lam_to_fix fixname body =
  match body.x with
  | VLam { lamarg; body } -> mk_fix fixname lamarg body
  | _ -> _die [%here]

let lam_to_fix_comp fixname body =
  value_to_term (lam_to_fix fixname (term_to_value body))

let mk_lete lhs rhs body = (CLetE { lhs; rhs; body }) #: body.ty

let mk_app appf apparg =
  (CApp { appf; apparg }) #: (snd @@ Nt.destruct_arr_tp appf.ty)

let mk_appop op appopargs =
  (CAppOp { op; appopargs }) #: (snd @@ Nt.destruct_arr_tp op.ty)

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

let erase_cty = function { nty; _ } -> nty

let rec erase_rty = function
  | RtyBase { cty; _ } -> erase_cty cty
  | RtyArr { argrty; retty; _ } ->
      Nt.mk_arr (erase_rty argrty) (erase_rty retty)
  | RtyProd (r1, r2) -> Nt.Ty_tuple [ erase_rty r1; erase_rty r2 ]

let is_base_rty = function RtyBase _ -> true | _ -> false

let destruct_base_rty = function
  | RtyBase { ou; cty } -> (ou, cty)
  | _ -> failwith "assume_base_rty"

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

let rec mk_rty_tuple = function
  | [] -> _die [%here]
  | [ x ] -> x
  | hd :: tl -> RtyProd (hd, mk_rty_tuple tl)

(** Denormalize *)

let rec typed_value_to_typed_raw_term (value_e : ('t, 't value) typed) =
  match value_e.x with
  | VConst constant0 -> (Const constant0) #: value_e.ty
  | VVar _t_stringtyped0 -> (Var _t_stringtyped0) #: value_e.ty
  | VLam { lamarg; body } ->
      (Lam { lamarg; lambody = typed_term_to_typed_raw_term body })
      #: value_e.ty
  | VFix { fixarg; body; _ } ->
      (* let tmp = (VLam { lamarg = fixarg; body }) #: body.ty in *)
      let tmp = (VLam { lamarg = fixarg; body }) #: value_e.ty in
      typed_value_to_typed_raw_term tmp
  | VTu _t__tvaluetypedlist0 ->
      (Tu (List.map typed_value_to_typed_raw_term _t__tvaluetypedlist0))
      #: value_e.ty

and typed_term_to_typed_raw_term (term_e : ('t, 't term) typed) =
  match term_e.x with
  | CErr -> Err #: term_e.ty
  | CVal _t__tvaluetyped0 -> typed_value_to_typed_raw_term _t__tvaluetyped0
  | CLetE { rhs; lhs; body } ->
      (Let
         {
           rhs = typed_term_to_typed_raw_term rhs;
           lhs = [ lhs ];
           letbody = typed_term_to_typed_raw_term body;
           if_rec = false;
         })
      #: term_e.ty
  | CLetDeTu { turhs; tulhs; body } ->
      (Let
         {
           rhs = typed_value_to_typed_raw_term turhs;
           lhs = tulhs;
           letbody = typed_term_to_typed_raw_term body;
           if_rec = false;
         })
      #: term_e.ty
  | CApp { appf; apparg } ->
      (App
         ( typed_value_to_typed_raw_term appf,
           [ typed_value_to_typed_raw_term apparg ] ))
      #: term_e.ty
  | CAppOp { op; appopargs } ->
      (AppOp (op, List.map typed_value_to_typed_raw_term appopargs))
      #: term_e.ty
  | CMatch { matched; match_cases } ->
      (Match
         {
           matched = typed_value_to_typed_raw_term matched;
           match_cases = List.map macth_case_to_raw_macth_case match_cases;
         })
      #: term_e.ty

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
