val get_num_arr : stlc_ty -> int
val gen_type : unit -> stlc_ty
val vars_with_type : stlc_tyctx -> stlc_ty -> stlc_term
val gen_term_no_app : stlc_tyctx -> stlc_ty -> stlc_term

let[@library] get_num_arr =
  let s = (true : [%v: stlc_ty]) [@over] in
  (num_arr s v : [%v: int]) [@under]

let[@library] gen_type =
  let s = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_ty]) [@under]

let[@library] gen_term_no_app =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && num_app v 0 : [%v: stlc_term]) [@under]

(* val oracle : int -> int -> stlc_tyctx -> stlc_ty -> stlc_term *)
(* val oracle_app : int -> int -> stlc_tyctx -> stlc_ty -> stlc_term *)
(* val oracle_abs : int -> int -> stlc_tyctx -> stlc_ty -> stlc_term *)

(* let[@library] oracle = *)
(*   let num_arr_tau = (true : [%v: int]) [@over] in *)
(*   let num = (true : [%v: int]) [@over] in *)
(*   let gamma = (true : [%v: stlc_tyctx]) [@over] in *)
(*   let tau = (true : [%v: stlc_ty]) [@over] in *)
(*   (typing gamma v tau && num_app v num : [%v: stlc_term]) [@under] *)

(* let[@library] oracle_app = *)
(*   let num_arr_tau = (true : [%v: int]) [@over] in *)
(*   let num = (true : [%v: int]) [@over] in *)
(*   let gamma = (true : [%v: stlc_tyctx]) [@over] in *)
(*   let tau = (true : [%v: stlc_ty]) [@over] in *)
(*   (is_app v && typing gamma v tau && num_app v num : [%v: stlc_term]) [@under] *)

(* let[@library] oracle_abs = *)
(*   let num_arr_tau = (true : [%v: int]) [@over] in *)
(*   let num = (true : [%v: int]) [@over] in *)
(*   let gamma = (true : [%v: stlc_tyctx]) [@over] in *)
(*   let tau = (true : [%v: stlc_ty]) [@over] in *)
(*   (is_abs v && typing gamma v tau && num_app v num : [%v: stlc_term]) [@under] *)

let rec gen_term_size (num_arr_tau : int) (num : int) (gamma : stlc_tyctx)
    (tau : stlc_ty) : stlc_term =
  if num == 0 then gen_term_no_app gamma tau
  else if bool_gen () then
    let (arg_tau : stlc_ty) = gen_type () in
    let (num_app_func : int) = int_range_inex 0 num in
    let (num_app_arg : int) = int_range_inex 0 (num - num_app_func) in
    let (func_ty : stlc_ty) = Stlc_ty_arr (arg_tau, tau) in
    let (num_arr_func_ty : int) = get_num_arr func_ty in
    let (func : stlc_term) =
      gen_term_size num_arr_func_ty num_app_func gamma
        (Stlc_ty_arr (arg_tau, tau))
    in
    let (num_arr_arg_ty : int) = get_num_arr arg_tau in
    let (arg : stlc_term) =
      gen_term_size num_arr_arg_ty num_app_arg gamma arg_tau
    in
    Stlc_app (func, arg)
  else
    match tau with
    | Stlc_ty_nat -> Err
    | Stlc_ty_arr (tau1, tau2) ->
        let (num_arr_tau2 : int) = get_num_arr tau2 in
        let (body : stlc_term) =
          gen_term_size num_arr_tau2 num (Stlc_tyctx_cons (tau1, gamma)) tau2
        in
        Stlc_abs (tau1, body)

let[@assert] gen_term_size =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && num_app v num : [%v: stlc_term]) [@under]
