open Language
open Zutils
open Zdatatype

let if_opt = false

let _simp_prop p =
  if if_opt then
    let res = SimplProp.eval_arithmetic p in
    let () =
      TypecheckerLog.typing @@ fun _ ->
      Pp.printf "@{<bold>SIMP@} %s =====> %s\n" (layout_prop p)
        (layout_prop res)
    in
    res
  else p

let exists_cty (x : string) ({ nty; phi } : 't cty) (cty : 't cty) : 't cty =
  if Nt.equal_nt Nt.unit_ty nty then { cty with phi = smart_add_to phi cty.phi }
  else
    let () =
      TypecheckerLog.typing @@ fun _ ->
      Pp.printf "@{<bold>exists_cty@} %s\n" (layout_prop phi)
    in
    let phi = subst_prop_instance default_v (AVar x#:nty) phi in
    let () =
      TypecheckerLog.typing @@ fun _ ->
      Pp.printf "@{<bold>exists_cty@} %s\n" (layout_prop phi)
    in
    let phi, cty_phi = map2 _simp_prop (phi, cty.phi) in
    let () =
      TypecheckerLog.typing @@ fun _ ->
      Pp.printf "@{<bold>exists_cty@} %s\n" (layout_prop phi)
    in
    let phi =
      if if_opt then smart_exists [ x#:nty ] (smart_add_to phi cty_phi)
      else Exists { qv = x#:nty; body = smart_add_to phi cty_phi }
    in
    let () =
      TypecheckerLog.typing @@ fun _ ->
      Pp.printf "@{<bold>exists_cty@} %s\n" (layout_prop phi)
    in
    let phi = if if_opt then SimplProp.simpl_query_by_eq phi else phi in
    { cty with phi }

let exists_rty (x : string) (xrty : 't rty) (rty : 't rty) : 't rty =
  match xrty with
  | RtyBase { ou = Under; cty = xcty } ->
      let dom =
        List.filter (fun var -> not @@ String.equal x var)
        @@ fv_rty_id rty @ fv_rty_id xrty
      in
      let rec aux (rty : 't rty) : 't rty =
        match rty with
        | RtyBase { ou = Over; _ } -> rty
        | RtyBase { ou = Under; cty } ->
            RtyBase { ou = Under; cty = exists_cty x xcty cty }
        | RtyArr { argrty; arg; retty } ->
            RtyArr { argrty = aux argrty; arg; retty = aux retty }
        | RtyPolyPred _ | RtyPolyType _ -> _die [%here]
      in
      let rty' = aux rty in
      let () =
        if not (is_close_rty dom rty') then (
          Printf.printf "rty: %s\n" (layout_rty rty);
          Printf.printf "%s: %s\n" x (layout_rty xrty);
          Printf.printf "exists: %s should closed under DOM[ %s ]\n"
            (layout_rty rty') (StrList.to_string dom);
          _die [%here])
      in
      rty'
  | _ -> rty

let exists_rty x rty =
  match x.ty with
  | RtyBase { ou = Under; cty } when Nt.equal_nt Nt.unit_ty cty.nty ->
      _assert [%here] "unit variable cannot be refered"
        (not @@ is_free_rty x.x rty);
      map_rty_retty (exists_cty x.x cty) rty
  | _ -> exists_rty x.x x.ty rty

let exists_rtys = List.fold_right exists_rty

let n_to_one_ctys prop_f = function
  | [] -> _die [%here]
  | { nty; phi } :: ctys ->
      if
        List.for_all (function { nty = nty'; _ } -> Nt.equal_nt nty nty') ctys
      then
        let phis = phi :: List.map (function { phi; _ } -> phi) ctys in
        let phis = List.map _simp_prop phis in
        { nty; phi = prop_f phis }
      else _die [%here]

let union_ctys = n_to_one_ctys smart_or

let rec union_rtys = function
  | [] -> _die [%here]
  | rty :: _ as rtys -> (
      match rty with
      | RtyBase { ou = Under; _ } ->
          let ctys =
            List.map
              (function
                | RtyBase { ou = Under; cty } -> cty | _ -> _die [%here])
              rtys
          in
          RtyBase { ou = Under; cty = union_ctys ctys }
      | RtyArr { argrty; _ } when Nt.equal_nt (erase_rty argrty) Nt.unit_ty ->
          let () =
            TypecheckerLog.typing @@ fun _ ->
            List.iter (fun rty -> Printf.printf "%s\n" (layout_rty rty)) rtys
          in
          let rtys = List.map (ret_ty [%here]) rtys in
          let rty = union_rtys rtys in
          mk_nfv_arr (mk_top_overrty Nt.unit_ty) rty
      | _ ->
          let () = Printf.printf "%s\n" (layout_rty rty) in
          _die [%here])
