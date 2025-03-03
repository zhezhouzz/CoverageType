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

let check_wf_rty (tau : 't rty) =
  let rec aux tau =
    match tau with
    | RtyBase _ -> ()
    | RtyArr { arr_type; argrty; arg; retty } -> (
        match (arr_type, argrty) with
        | GhostOverBaseArr, RtyBase { ou = Over; _ } -> ()
        | GhostOverBaseArr, _ -> _die_with [%here] "Rty is not well-fromed"
        | NormalArr, RtyBase { ou = Over; _ } -> ()
        | NormalArr, _ ->
            if is_free_rty arg retty then
              _die_with [%here] "Rty is not well-fromed")
    | RtyProd (tau1, tau2) ->
        aux tau1;
        aux tau2
  in
  aux tau

let constant_to_value c = (VConst c) #: (Prop.constant_to_nt c)
let value_to_term v = (CVal v) #: v.ty
let term_to_value e = match e.x with CVal v -> v.x #: e.ty | _ -> _die [%here]
let id_to_value v = (VVar v) #: v.ty
let id_to_term v = value_to_term @@ id_to_value v

let map_rty_retty f rty =
  let rec aux rty =
    match rty with
    | RtyBase _ -> f rty
    | RtyArr { arr_type; argrty; arg; retty } ->
        RtyArr { arr_type; argrty; arg; retty = f retty }
    | RtyProd (r1, r2) -> RtyProd (aux r1, aux r2)
  in
  aux rty

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
let mk_app appf apparg = (CApp { appf; apparg }) #: (Nt.get_arr_rhs appf.ty)

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

let mk_top_cty nty = { nty; phi = Prop.mk_true }
let mk_bot_cty nty = { nty; phi = Prop.mk_false }
let cty_to_overrty cty = RtyBase { ou = Over; cty }
let cty_to_underrty cty = RtyBase { ou = Under; cty }
let mk_top_overrty nty = cty_to_overrty @@ mk_top_cty nty
let mk_bot_overrty nty = cty_to_overrty @@ mk_bot_cty nty
let mk_top_underrty nty = cty_to_underrty @@ mk_top_cty nty
let mk_bot_underrty nty = cty_to_underrty @@ mk_bot_cty nty

let mk_unit_underrty phi =
  RtyBase { ou = Under; cty = { nty = Nt.unit_ty; phi } }

open Prop

let value_to_lit loc = function
  | VVar x -> AVar x
  | VConst c -> AC c
  | _ -> _die loc

let mk_eq_var_prop x = lit_to_prop (mk_var_eq_var [%here] default_v #: x.ty x)

let mk_eq_c_prop c =
  lit_to_prop (mk_var_eq_c [%here] default_v #: (constant_to_nt c) c)

let mk_eq_tvar_cty x = { nty = x.ty; phi = mk_eq_var_prop x }
let mk_eq_c_cty c = { nty = constant_to_nt c; phi = mk_eq_c_prop c }
let mk_eq_tvar_overrty x = RtyBase { ou = Over; cty = mk_eq_tvar_cty x }
let mk_eq_tvar_underrty x = RtyBase { ou = Under; cty = mk_eq_tvar_cty x }
let mk_eq_c_overrty x = RtyBase { ou = Over; cty = mk_eq_c_cty x }
let mk_eq_c_underrty x = RtyBase { ou = Under; cty = mk_eq_c_cty x }

let destruct_grty =
  let rec aux rty =
    match rty with
    | RtyBase _ | RtyProd _ | RtyArr { arr_type = NormalArr; _ } -> ([], rty)
    | RtyArr { arr_type = GhostOverBaseArr; argrty; arg; retty } ->
        let arg' = Rename.unique arg in
        let retty =
          subst_rty_instance arg (AVar arg' #: (erase_rty argrty)) retty
        in
        let gvars, res = aux retty in
        ((arg' #: argrty) :: gvars, res)
  in
  aux

let construct_grty gvars rty =
  List.fold_right
    (fun x retty ->
      RtyArr { arr_type = GhostOverBaseArr; argrty = x.ty; arg = x.x; retty })
    gvars rty

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
  | VTuple _t__tvaluetypedlist0 ->
      (Tuple (List.map typed_value_to_typed_raw_term _t__tvaluetypedlist0))
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
  | CLetDeTuple { turhs; tulhs; body } ->
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

(* Typectx *)

open Typectx

let rty_add_to_right { builtin_ctx; axioms } x =
  { builtin_ctx = add_to_right builtin_ctx x; axioms }

let axiom_add_to_right { builtin_ctx; axioms } x =
  { builtin_ctx; axioms = add_to_right axioms x }

let rty_add_to_rights { builtin_ctx; axioms } x =
  { builtin_ctx = add_to_rights builtin_ctx x; axioms }

let axiom_add_to_rights { builtin_ctx; axioms } x =
  { builtin_ctx; axioms = add_to_rights axioms x }

let bctx_to_axioms bctx = List.map _get_ty @@ ctx_to_list bctx.axioms
