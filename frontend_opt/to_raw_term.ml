open Zutils
open OcamlParser
open Mutils
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar

let typed_to_expr f expr =
  match expr.ty with
  | Nt.Ty_unknown -> f expr.x
  | _ ->
      desc_to_ocamlexpr @@ Pexp_constraint (f expr.x, Nt.t_to_core_type expr.ty)

let typed_id_to_pattern id =
  let pat = string_to_pattern id.x in
  match id.ty with
  | Nt.Ty_unknown -> pat
  | _ -> typed_to_pattern (pat, Nt.t_to_core_type id.ty)

let typed_ids_to_pattern ids =
  Ast_helper.Pat.tuple (List.map typed_id_to_pattern ids)

let rec typed_raw_term_to_expr expr = typed_to_expr raw_term_to_expr expr

and raw_term_to_expr (expr : Nt.t raw_term) =
  match expr with
  | Err -> mk_construct ("Err", [])
  | Tuple es ->
      desc_to_ocamlexpr @@ Pexp_tuple (List.map typed_raw_term_to_expr es)
  | Var var -> typed_to_expr mkvar var
  | Const v -> constant_to_expr v
  | Let { if_rec; lhs; rhs; letbody } ->
      let flag = if if_rec then Asttypes.Recursive else Asttypes.Nonrecursive in
      let vb = mk_vb (typed_ids_to_pattern lhs, typed_raw_term_to_expr rhs) in
      desc_to_ocamlexpr
      @@ Pexp_let (flag, [ vb ], typed_raw_term_to_expr letbody)
  | AppOp (op, args) ->
      (* NOTE: to make the printed code looks clearer, we don't print type of operators. *)
      mk_op_apply (layout_op op.x, List.map typed_raw_term_to_expr args)
  | App (func, args) ->
      (* NOTE: to make the printed code looks clearer, we don't print type of function in its application. *)
      let func = raw_term_to_expr func.x in
      let args =
        List.map (fun x -> (Asttypes.Nolabel, typed_raw_term_to_expr x)) args
      in
      desc_to_ocamlexpr @@ Pexp_apply (func, args)
  | Ifte (e1, e2, e3) ->
      let e1, e2, e3 = map3 typed_raw_term_to_expr (e1, e2, e3) in
      desc_to_ocamlexpr @@ Pexp_ifthenelse (e1, e2, Some e3)
  | Match { matched; match_cases } ->
      desc_to_ocamlexpr
      @@ Pexp_match
           ( typed_raw_term_to_expr matched,
             List.map match_case_to_expr match_cases )
  | Lam { lamarg; lambody } ->
      mklam (typed_id_to_pattern lamarg) (typed_raw_term_to_expr lambody)

and match_case_to_expr = function
  | Matchcase { constructor; args; exp } ->
      (* NOTE: to make the printed code looks clearer, we don't print type of data constructors. *)
      let pc_lhs =
        string_dataconstr_to_pattern
          (constructor.x, List.map (fun x -> string_to_pattern x.x) args)
      in
      { pc_lhs; pc_guard = None; pc_rhs = typed_raw_term_to_expr exp }

open Sugar

(* let id_to_var id = (fun x -> Var x) #-> id *)

let update_ty { x; ty } ty' =
  match ty with Nt.Ty_unknown -> x #: ty' | _ -> x #: ty'

type 't term_or_op =
  | C_is_term of ('t, 't raw_term) typed
  | C_is_op of ('t, op) typed

let constructor_to_term_or_op c =
  match c with
  | "Err" | "Exn" -> C_is_term Err #: Nt.Ty_any
  | "true" | "false" | "()" ->
      C_is_term { x = Const (string_to_constant c); ty = Nt.Ty_unknown }
  | name -> (
      match string_to_op_opt name with
      | None -> _failatwith [%here] "die: pat"
      | Some op -> C_is_op op #: Nt.Ty_unknown)

(* TODO: Check nested tuple *)
let to_typed_ids x =
  let rec aux l x =
    match x.x with
    | Var y -> l @ [ { ty = x.ty; x = y.x } ]
    | Tuple xs -> List.fold_left aux l xs
    | _ -> failwith "not a pattern"
  in
  aux [] x

let de_tuple_term e = match e.x with Tuple xs -> xs | _ -> [ e ]

let term_force_var e =
  match e.x with
  | Var x -> x
  | _ -> _failatwith [%here] "fail to convert a term to a variable"

let rec typed_raw_term_of_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_tuple ps ->
      (Tuple (List.map typed_raw_term_of_pattern ps)) #: Nt.Ty_unknown
  | Ppat_var ident -> (Var ident.txt #: Nt.Ty_unknown) #: Nt.Ty_unknown
  | Ppat_constraint (ident, tp) ->
      let term = typed_raw_term_of_pattern ident in
      term.x #: (Nt.core_type_to_t tp)
  | Ppat_construct (c, args) -> (
      let c = longid_to_id c in
      match constructor_to_term_or_op c with
      | C_is_term tm -> tm
      | C_is_op op ->
          let args =
            match args with
            | None -> []
            | Some args ->
                de_tuple_term @@ typed_raw_term_of_pattern @@ snd args
          in
          (AppOp (op, args)) #: Nt.Ty_unknown)
  | Ppat_any -> (Var "_" #: Nt.Ty_unknown) #: Nt.Ty_unknown
  | _ ->
      Pprintast.pattern Format.std_formatter pattern;
      failwith "wrong pattern name, maybe untyped"

let typed_ids_of_pattern pattern =
  to_typed_ids @@ typed_raw_term_of_pattern pattern

let typed_raw_term_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_tuple es -> (Tuple (List.map aux es)) #: Nt.Ty_unknown
    | Pexp_constraint (expr, ty) ->
        (* let () = Printf.printf "Pexp_constraint: %s\n" (layout_ct ty) in *)
        update_ty (aux expr) (Nt.core_type_to_t ty)
    | Pexp_ident id -> (Var (longid_to_id id) #: Nt.Ty_unknown) #: Nt.Ty_unknown
    | Pexp_construct (c, args) -> (
        let args =
          match args with
          | None -> []
          | Some args -> (
              let args = aux args in
              match args.x with Tuple es -> es | _ -> [ args ])
        in
        let c = constructor_to_term_or_op @@ longid_to_id c in
        match c with
        | C_is_term tm -> tm
        | C_is_op op -> (AppOp (op, args)) #: Nt.Ty_unknown)
    | Pexp_constant _ -> (Const (expr_to_constant expr)) #: Nt.Ty_unknown
    | Pexp_let (flag, vbs, e) ->
        List.fold_right
          (fun vb letbody ->
            (Let
               {
                 if_rec = get_if_rec flag;
                 lhs = typed_ids_of_pattern vb.pvb_pat;
                 rhs = aux vb.pvb_expr;
                 letbody;
               })
            #: Nt.Ty_unknown)
          vbs (aux e)
    | Pexp_apply (func, args) ->
        let args = List.map (fun x -> aux @@ snd x) args in
        let func = aux func in
        let res =
          match func.x with
          | Var f -> (
              match string_to_op_opt f.x with
              | Some op ->
                  let op = op #: f.ty in
                  AppOp (op, args)
              | None -> App (func, args))
          | _ -> App (func, args)
        in
        res #: Nt.Ty_unknown
    | Pexp_ifthenelse (e1, e2, Some e3) ->
        (Ifte (aux e1, aux e2, aux e3)) #: Nt.Ty_unknown
    | Pexp_ifthenelse (e1, e2, None) ->
        (Ifte (aux e1, aux e2, (Const U) #: Nt.unit_ty)) #: Nt.Ty_unknown
    | Pexp_match (matched, match_cases) ->
        let match_cases =
          List.map
            (fun case ->
              match (typed_raw_term_of_pattern case.pc_lhs).x with
              | AppOp ({ x = DtConstructor op; ty }, args) ->
                  Matchcase
                    {
                      constructor = { x = op; ty };
                      args = List.map term_force_var args;
                      exp = aux case.pc_rhs;
                    }
              | _ -> _failatwith [%here] "?")
            match_cases
        in
        (Match { matched = aux matched; match_cases }) #: Nt.Ty_unknown
    | Pexp_fun (_, _, arg0, expr) ->
        let arg = typed_raw_term_of_pattern arg0 in
        let () =
          match arg.ty with
          | Nt.Ty_unknown ->
              failwith
                (spf "Syntax error: lambda function should provide types (%s)"
                   (layout_ arg0))
          | _ -> ()
        in
        let lamarg =
          match arg.x with
          | Var x -> x.x #: arg.ty
          | _ ->
              let () = Printf.printf "%s\n" (layout_ arg0) in
              failwith "Syntax error: lambda function wrong argument"
        in
        (Lam { lamarg; lambody = aux expr }) #: Nt.Ty_unknown
        (* un-curry *)
    | Pexp_sequence (e1, e2) ->
        let lhs = [ { x = Rename.unique "unused"; ty = Nt.unit_ty } ] in
        let rhs = aux e1 in
        let letbody = aux e2 in
        (Let { if_rec = false; lhs; rhs; letbody }) #: Nt.Ty_unknown
    | _ ->
        raise
        @@ failwith
             (Sugar.spf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  in
  aux expr

let raw_term_of_expr expr = (typed_raw_term_of_expr expr).x

let typed_id_of_expr expr =
  let x = typed_raw_term_of_expr expr in
  match x.x with
  | Var id -> id #: x.ty
  | _ ->
      _failatwith [%here] (spf "die: %s" (Pprintast.string_of_expression expr))

let id_of_expr expr = (typed_id_of_expr expr).x
let layout_raw_term x = Pprintast.string_of_expression @@ raw_term_to_expr x

let layout_typed_raw_term x =
  Pprintast.string_of_expression @@ raw_term_to_expr x.x

let layout_omit_type x = layout_raw_term @@ (typed_raw_term_of_expr x).x
let layout_typed_term x = layout_typed_raw_term @@ denormalize_term x
let layout_term x = layout_typed_raw_term @@ denormalize_term x #: Nt.Ty_unknown
let layout_typed_value x = layout_typed_raw_term @@ denormalize_value x

let layout_value x =
  layout_typed_raw_term @@ denormalize_value x #: Nt.Ty_unknown
