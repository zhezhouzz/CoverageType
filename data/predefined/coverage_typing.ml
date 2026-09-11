(** Premitive type *)

let[@library] TT = (true : [%v: unit]) [@under]
let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]
let[@library] None = fun (a : baseType) -> (v == None : [%v: 'a option])

let[@library] Some =
 fun (a : baseType) ?r:(x : 'a) -> (v == Some x : [%v: 'a option])

let[@library] fst =
 fun (a : baseType) (b : baseType) ?r:(x : 'a * 'b) -> (v == fst x : [%v: 'a])

let[@library] snd =
 fun (a : baseType) (b : baseType) ?r:(x : 'a * 'b) -> (v == snd x : [%v: 'b])

(** Arithmatic operators *)

let[@library] ( == ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == (a == b) : [%v: bool])

let[@library] ( != ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == (a != b) : [%v: bool])

let[@library] ( < ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == (a < b) : [%v: bool])

let[@library] ( > ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == (a > b) : [%v: bool])

let[@library] ( <= ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == (a <= b) : [%v: bool])

let[@library] ( >= ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == (a >= b) : [%v: bool])

let[@library] ( + ) = fun ?r:(a : int) ?r:(b : int) -> (v == a + b : [%v: int])
let[@library] ( - ) = fun ?r:(a : int) ?r:(b : int) -> (v == a - b : [%v: int])
let[@library] ( * ) = fun ?r:(a : int) ?r:(b : int) -> (v == a * b : [%v: int])

let[@library] ( / ) =
 fun ?r:(a : int) ?r:(b = ((v != 0 : [%v: int]) [@over])) ->
  (v == a / b : [%v: int])

let[@library] ( mod ) =
 fun ?r:(a : int) ?r:(b = ((v != 0 : [%v: int]) [@over])) ->
  (v == a mod b : [%v: int])

let[@library] not = fun ?r:(a : bool) -> (v == not a : [%v: bool])

let[@library] ( && ) =
 fun ?r:(a : bool) ?r:(b : bool) -> (v == (a && b) : [%v: bool])

let[@library] ( || ) =
 fun ?r:(a : bool) ?r:(b : bool) -> (v == (a || b) : [%v: bool])

(** Builtin generators *)

let[@library] bool_gen = M (true : [%v: bool])
let[@library] int_gen = M (true : [%v: int])
let[@library] nat_gen = M (0 <= v : [%v: int])

let[@library] int_range_inc =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((a <= v : [%v: int]) [@over]) in
  ((a <= v && v <= b : [%v: int]) [@under])

let[@library] int_range_inex =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((a <= v : [%v: int]) [@over]) in
  ((a <= v && v < b : [%v: int]) [@under])

let[@library] increment =
  let n = ((true : [%v: int]) [@over]) in
  ((v == n + 1 : [%v: int]) [@under])

let[@library] decrement =
  let n = ((true : [%v: int]) [@over]) in
  ((v == n - 1 : [%v: int]) [@under])

let[@library] lt_eq_one =
  let s = ((true : [%v: int]) [@over]) in
  (v == (s <= 1) && iff (not v) (s > 1) : [%v: bool])

let[@library] gt_eq_int_gen =
  let x = ((true : [%v: int]) [@over]) in
  ((true : [%v: int]) [@under])

let[@library] sizecheck =
  let x = ((true : [%v: int]) [@over]) in
  (v == (x == 0) && iff (not v) (x > 0) : [%v: bool])

let[@library] subs =
  let s = ((true : [%v: int]) [@over]) in
  ((v == s - 1 : [%v: int]) [@under])

let[@library] dummy = (true : [%v: unit])

(** Datatypes and method predicates (needs to be stratificated) *)

(** lists *)

let[@library] Nil = fun (a : baseType) -> (list_len v == 0 : [%v: 'a list])

let[@library] Cons =
 fun (a : baseType) ?r:(x : 'a) ?r:(xs : 'a list) ->
  (hd v x && tl v xs : [%v: 'a list])

let[@library] list_mem =
 fun (a : baseType) ?r:(xs : 'a list) ?r:(x : 'a) ->
  (v == list_mem xs x : [%v: bool])

let[@library] list_length =
 fun (a : baseType) ?r:(xs : 'a list) -> (v == list_len xs : [%v: int])

let[@library] list_nth =
 fun (a : baseType) ?r:(xs : 'a list)
     ?r:(idx = ((0 <= v && v < list_len xs : [%v: int]) [@over])) ->
  (list_nth_pred xs idx v : [%v: 'a])

(** Tree *)

let[@library] Leaf = fun (a : baseType) -> (depth v == 0 : [%v: 'a tree])

let[@library] Node =
 fun (a : baseType) ?r:(x : 'a) ?r:(lt : 'a tree) ?r:(rt : 'a tree) ->
  (root v x && lch v lt && rch v rt : [%v: 'a tree])

(** Elrond *)

let[@library] Streamnil =
 fun (a : baseType) -> (stream_len v == 0 : [%v: 'a stream])

let[@library] Streamlazycons =
 fun (a : baseType) ?r:(x : 'a) ?r:(xs : 'a stream lazyty) ->
  (stream_hd v x && stream_tl v (forc xs) : [%v: 'a stream])

let[@library] Lazyty =
 fun (a : baseType) ?r:(x : 'a stream) -> (forc v == x : [%v: 'a stream lazyty])

let[@library] Lhpleaf =
 fun (a : baseType) -> (leftisthp_depth v == 0 : [%v: 'a leftisthp])

let[@library] Lhpnode =
 fun (a : baseType) ?r:(rk : int) ?r:(x : 'a) ?r:(lt : 'a leftisthp)
     ?r:(rt : 'a leftisthp) ->
  (leftisthp_rank v rk && leftisthp_root v x && leftisthp_lch v lt
   && leftisthp_rch v rt
    : [%v: 'a leftisthp])

let[@library] Rbtleaf = fun (a : baseType) -> (rb_leaf v : [%v: 'a rbtree])

let[@library] Rbtnode =
 fun (a : baseType) ?r:(c : bool) ?r:(lt : 'a rbtree) ?r:(x : 'a)
     ?r:(rt : 'a rbtree) ->
  ((rb_root_color v c && rb_root v x && rb_lch v lt && rb_rch v rt
    : [%v: 'a rbtree])
    [@under])

(** STLC *)

let[@library] Stlc_ty_nat = (num_arr v == 0 : [%v: stlc_ty])

let[@library] Stlc_ty_arr =
 fun ?r:(t1 : stlc_ty) ?r:(t2 : stlc_ty) ->
  (stlc_ty_arr1 v t1 && stlc_ty_arr2 v t2 : [%v: stlc_ty])

let[@library] Stlc_const =
 fun ?r:(n : int) -> (stlc_const v n : [%v: stlc_term])

let[@library] Stlc_id = fun ?r:(n : int) -> (stlc_id v n : [%v: stlc_term])

let[@library] Stlc_app =
 fun ?r:(t1 : stlc_term) ?r:(t2 : stlc_term) ->
  (stlc_app1 v t1 && stlc_app2 v t2 : [%v: stlc_term])

let[@library] Stlc_abs =
 fun ?r:(ty : stlc_ty) ?r:(body : stlc_term) ->
  (stlc_abs_ty v ty && stlc_abs_body v body : [%v: stlc_term])

(** VeLLVM *)

let[@library] TYPE_I = fun ?r:(i : int) -> (type_i v i : [%v: typ])
let[@library] TYPE_Void = (type_void v : [%v: typ])

let[@library] TYPE_Vector =
 fun ?r:(i : int) ?r:(ty : typ) ->
  (type_vector1 v i && type_vector2 v ty : [%v: typ])

let[@library] TYPE_Array =
 fun ?r:(i : int) ?r:(ty : typ) ->
  (type_array1 v i && type_array2 v ty : [%v: typ])

let[@library] TYPE_Others = (type_others v : [%v: typ])

let[@library] DVALUE_I =
 fun ?r:(s : int) ?r:(i : int) ->
  (dvalue_int_size v s && dvalue_int_content v i : [%v: dvalue])

let[@library] DVALUE_None = (dvalue_none v : [%v: dvalue])

let[@library] DVALUE_Vector =
 fun ?r:(ty : typ) ?r:(cnt : dvalue list) ->
  (dvalue_vector_typ v ty && dvalue_vector_content v cnt : [%v: dvalue])

let[@library] DVALUE_Array =
 fun ?r:(ty : typ) ?r:(cnt : dvalue list) ->
  (dvalue_array_typ v ty && dvalue_array_content v cnt : [%v: dvalue])

let[@library] DVALUE_Others = (dvalue_others v : [%v: dvalue])

(** Herdtool7 *)

let[@library] L_Int = fun ?r:(i : int) -> (herd_l_int v i : [%v: literal])
let[@library] L_Bool = fun ?r:(i : bool) -> (herd_l_bool v i : [%v: literal])
let[@library] L_Real = fun ?r:(i : float) -> (herd_l_real v i : [%v: literal])

let[@library] L_BitVector =
 fun ?r:(i : char list) -> (herd_l_bitvector v i : [%v: literal])

let[@library] L_String =
 fun ?r:(i : string) -> (herd_l_string v i : [%v: literal])

(** Zipperposition *)

let[@library] PT_Var = fun ?r:(s : string) -> (pt_var v s : [%v: pt_term])

let[@library] PT_App =
 fun ?r:(tr1 : pt_term) ?r:(tr2 : pt_term list) ->
  (pt_app v tr1 tr2 : [%v: pt_term])

let[@library] PT_Ite =
 fun ?r:(tr1 : pt_term) ?r:(tr2 : pt_term) ?r:(tr3 : pt_term) ->
  (pt_ite v tr1 tr2 tr3 : [%v: pt_term])

(** Aux functions *)

(** For frequency *)

let[@library] sum_fst_int =
 fun (a : baseType) ?r:(xs : (int * 'a) list) -> (0 <= v : [%v: int])

let[@library] choose_by_fq =
 fun ?r:(xs : int list) -> (0 <= v && v < list_len xs : [%v: int])

let[@library] char_of_int =
 fun ?r:(x : int) -> (x == char_to_int v : [%v: char])

let[@library] swap =
 fun (a : baseType) ?r:(l : 'a list)
     ?r:(i = ((0 <= v && v < list_len l : [%v: int]) [@over]))
     ?r:(j = ((0 <= v && v < list_len l : [%v: int]) [@over])) ->
  (true : [%v: 'a list])
