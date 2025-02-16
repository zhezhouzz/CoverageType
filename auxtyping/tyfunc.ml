open Language
open Zutils
open Zdatatype

let exists_cty (x : string) ({ nty; phi } : 't cty) (cty : 't cty) : 't cty =
  match nty with
  | Nt.Ty_unit -> { cty with phi = smart_add_to phi cty.phi }
  | _ ->
      let phi = subst_prop_instance default_v (AVar x #: nty) phi in
      { cty with phi = smart_exists [ x #: nty ] (smart_add_to phi cty.phi) }

let exists_rty (x : string) (xrty : 't rty) (rty : 't rty) : 't rty =
  let dom =
    List.filter (fun var -> not @@ String.equal x var)
    @@ fv_rty_id rty @ fv_rty_id xrty
  in
  let xcty =
    match xrty with RtyBase { ou = Under; cty } -> cty | _ -> _die [%here]
  in
  let rec aux (rty : 't rty) : 't rty =
    match rty with
    | RtyBase { ou = Over; _ } -> rty
    | RtyBase { ou = Under; cty } ->
        RtyBase { ou = Under; cty = exists_cty x xcty cty }
    | RtyArr { arr_type; argrty; arg; retty } ->
        RtyArr { arr_type; argrty = aux argrty; arg; retty = aux retty }
    | RtyProd _ -> _die_with [%here] "unimp"
  in
  let rty = aux rty in
  let () =
    _assert [%here]
      (spf "exists: %s should closed under DOM[ %s ]" (layout_rty rty)
         (StrList.to_string dom))
    @@ is_close_rty dom rty
  in
  rty

let exists_rty x rty =
  match x.ty with
  | RtyBase { ou = Under; cty = { nty = Nt.Ty_unit; _ } } ->
      _assert [%here] "unit variable cannot be refered"
        (not @@ is_free_rty x.x rty);
      map_rty_retty (exists_rty x.x x.ty) rty
  | _ -> exists_rty x.x x.ty rty

let exists_rtys = List.fold_right exists_rty

let n_to_one_ctys prop_f = function
  | [] -> _die [%here]
  | { nty; phi } :: ctys ->
      if
        List.for_all (function { nty = nty'; _ } -> Nt.equal_nt nty nty') ctys
      then
        let phi =
          prop_f (phi :: List.map (function { phi; _ } -> phi) ctys)
        in
        { nty; phi }
      else _die [%here]

let union_ctys = n_to_one_ctys smart_or

let union_rtys = function
  | [] -> _die [%here]
  | _ as rtys ->
      let ctys =
        List.map
          (function RtyBase { ou = Under; cty } -> cty | _ -> _die [%here])
          rtys
      in
      RtyBase { ou = Under; cty = union_ctys ctys }
