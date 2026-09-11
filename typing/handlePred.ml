open Language
open Zutils
open Sugar
open Zdatatype

(** The module handles the poly predicates.
    A Subtyping Unification Algorithm: for given rty1 <: rty2, we instantiate poly predicate in rty2 according to the rty1.
    forall p1.{v: X | p1 v} <: forall p2.{v: X | p2 v} will create constraint p2(v) = p1(v).
    solution: p2 = fun v -> p1(v)
    result is forall p1. forall p2.{v: X | p1 v}
    simplified as forall p1.{v: X | p1 v}
*)

(** Solution is a function *)

type solution = { args : (Nt.t, string) typed list; body : Nt.t prop }

let layout_solution (p, sol) =
  spf "%s(%s) := %s" p
    (List.split_by_comma _get_x sol.args)
    (layout_prop sol.body)

let layaout_solutions m =
  List.split_by ";; " layout_solution @@ StrMap.to_kv_list m

let instantiate_lit (p, sol) lit =
  TypecheckerLog.instantiate_rty (fun () ->
      Printf.printf "instantiate_lit %s in %s\n" p (layout_lit lit.x));
  match lit.x with
  | AAppOp (op, args) when String.equal p op.x ->
      let l = _safe_combine [%here] sol.args args in
      let l =
        List.map
          (fun (x, lit) ->
            _assert [%here]
              (spf "instantiate: basic type should be equal: %s != %s"
                 (Nt.layout x.ty) (Nt.layout lit.ty))
              (Nt.equal_nt x.ty lit.ty);
            (x.x, lit.x))
          l
      in
      let phi = msubst subst_prop_instance l sol.body in
      phi
  | _ -> Lit lit

let instantiate_prop (p, sol) =
  let rec aux prop =
    match prop with
    | Implies (p1, p2) -> Implies (aux p1, aux p2)
    | Ite (p1, p2, p3) -> Ite (aux p1, aux p2, aux p3)
    | Not p -> Not (aux p)
    | And ps -> And (List.map aux ps)
    | Or ps -> Or (List.map aux ps)
    | Iff (p1, p2) -> Iff (aux p1, aux p2)
    | Forall { qv; body } -> Forall { qv; body = aux body }
    | Exists { qv; body } -> Exists { qv; body = aux body }
    | Lit lit -> instantiate_lit (p, sol) lit
  in
  aux

let instantiate_rty (p, sol) =
  let rec aux rty =
    match rty with
    | RtyBase { ou; cty } ->
        RtyBase
          { ou; cty = { cty with phi = instantiate_prop (p, sol) cty.phi } }
    | RtyArr { argrty; arg; retty } ->
        RtyArr { argrty = aux argrty; arg; retty = aux retty }
    | RtyPolyType _ | RtyPolyPred _ -> _die [%here]
  in
  aux

let instantiate_solutions (p, sol) m =
  StrMap.map
    (fun { args; body } -> { args; body = instantiate_prop (p, sol) body })
    m

let instantiate_cs (p, sol) cs = List.map (map2 (instantiate_rty (p, sol))) cs

let minstantiate_rty m rty =
  msubst (fun p v -> instantiate_rty (p, v)) (StrMap.to_kv_list m) rty

(** Check is a base type is poly predicate qualified *)

let unique_pds poly_preds =
  List.slow_rm_dup (fun a b -> String.equal a.x b.x) poly_preds

let as_poly_pred_quafilied_lit pds lit =
  let open Prop in
  match lit.x with
  | AAppOp (p, args) ->
      let pds' = List.filter (fun x -> not (String.equal x.x p.x)) pds in
      if List.length pds' < List.length pds then
        let args =
          List.map
            (fun x ->
              match x.x with
              | AVar x -> x
              | _ ->
                  _die_with [%here]
                    (spf "invalid poly pred application (%s)" (layout_lit lit.x)))
            args
        in
        Some (p.x, args)
      else None
  | _ -> None

let as_poly_pred_quafilied_cty pds cty =
  let open Prop in
  match cty.phi with Lit lit -> as_poly_pred_quafilied_lit pds lit | _ -> None

let unification_rtys poly_preds cs =
  let poly_preds = unique_pds poly_preds in
  let rec aux m cs =
    match cs with
    | [] -> m
    | (t1, t2) :: cs -> (
        match (t1, t2) with
        | RtyBase { cty = cty1; _ }, RtyBase { cty = cty2; _ } -> (
            if not (Nt.equal_nt cty1.nty cty2.nty) then (
              Printf.printf
                "instantiate: basic type should be equal\n\
                 %s != %s\n\
                 Precisely:\n\
                 %s != %s"
                (Nt.layout_nt cty1.nty) (Nt.layout_nt cty2.nty)
                (Nt.show_nt cty1.nty) (Nt.show_nt cty2.nty);
              _die [%here]);
            match as_poly_pred_quafilied_cty poly_preds cty2 with
            | None -> (
                match as_poly_pred_quafilied_cty poly_preds cty1 with
                | None -> aux m cs
                | Some (p, args) ->
                    let sol = { args; body = cty2.phi } in
                    let m = instantiate_solutions (p, sol) m in
                    let cs = instantiate_cs (p, sol) cs in
                    aux (StrMap.add p sol m) cs)
            | Some (p, args) ->
                let sol = { args; body = cty1.phi } in
                let m = instantiate_solutions (p, sol) m in
                let cs = instantiate_cs (p, sol) cs in
                aux (StrMap.add p sol m) cs)
        | ( RtyArr { argrty = argrty1; arg = arg1; retty = retty1 },
            RtyArr { argrty = argrty2; arg = arg2; retty = retty2 } ) ->
            _assert [%here] "all name shoudl be fresh"
              (not (String.equal arg1 arg2));
            let retty1 =
              subst_rty_instance arg1 (AVar arg2#:(erase_rty argrty1)) retty1
            in
            aux m ((argrty1, argrty2) :: (retty1, retty2) :: cs)
        | _, _ ->
            Printf.printf "rty1: %s\nrty2: %s\n" (layout_rty t1) (layout_rty t2);
            _die [%here])
  in
  let m = aux StrMap.empty cs in
  if StrMap.is_empty m then None
  else
    let poly_preds =
      List.filter (fun pd -> not (StrMap.mem pd.x m)) poly_preds
    in
    Some (poly_preds, m)

let instantiate_poly_pred_rty_aux pds frty xrty =
  let () =
    TypecheckerLog.instantiate_rty (fun () ->
        Printf.printf "instantiate %s\nwith %s\n"
          (layout_rty (construct_poly_pred_rty (pds, frty)))
          (layout_rty xrty))
  in
  let argrty, arg, retty =
    match frty with
    | RtyArr { argrty; arg; retty } -> (argrty, arg, retty)
    | _ -> _die [%here]
  in
  let* pds, m = unification_rtys pds [ (xrty, argrty) ] in
  let () =
    TypecheckerLog.instantiate_rty (fun () ->
        Printf.printf "solution:\n%s\n" (layaout_solutions m))
  in
  let argrty = minstantiate_rty m argrty in
  (* let retty = *)
  (*   if Nt.is_base_tp (erase_rty argrty) then *)
  (*     subst_rty_instance arg (value_to_lit [%here] x.x) retty *)
  (*   else retty *)
  (* in *)
  let retty = minstantiate_rty m retty in
  let rty = RtyArr { argrty; arg; retty } in
  let xrty = minstantiate_rty m xrty in
  let () =
    TypecheckerLog.instantiate_rty (fun () ->
        Printf.printf "instantiated rty: %s\n" (layout_rty rty);

        Printf.printf "instantiated xrty: %s\n" (layout_rty xrty);
        Printf.printf "pds: %s\n" (List.split_by_comma _get_x pds))
  in
  Some (pds, rty, xrty)

let instantiate_poly_pred_rty predctx frty xty =
  let pds, frty = lift_poly_pred_rty frty in
  let xpds, xrty = lift_poly_pred_rty xty in
  let pds = pds @ xpds in
  let () =
    _assert [%here] "poly predicates are unique"
      (List.length pds == List.length (unique_pds pds))
  in
  let m =
    List.fold_left
      (fun m pred ->
        match Typectx.get_opt predctx pred.x with
        | None -> m
        | Some _ -> (pred.x, Rename.unique_var pred.x) :: m)
      [] pds
  in
  let pds =
    List.map
      (fun p ->
        msubst
          (fun x x' pd -> if String.equal x pd.x then x'#:pd.ty else pd)
          m p)
      pds
  in
  let frty = msubst rename_pred_rty m frty in
  let xrty = msubst rename_pred_rty m xrty in
  match instantiate_poly_pred_rty_aux pds frty xrty with
  | None -> (pds, frty, xty)
  | Some (pds, rty, xrty) -> (pds, rty, xrty)
