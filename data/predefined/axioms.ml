(** We always use 'a as poly type in the axioms *)

(** Axioms *)

(** Rational *)

let[@axiom] rational_zero_one =
 fun (v : int * int) ->
  (rational_zero_one v)#==>(0 <= fst v
                           && fst v <= snd v
                           && 1 <= snd v
                           && snd v <= 2147483647)

(** Priority *)

let[@axiom] ex_priority_list_3 =
 fun ((e1 [@ex]) : priority) ((e2 [@ex]) : priority) ((e3 [@ex]) : priority)
     ((e3list [@ex]) : (int * int) list) ((lemp [@ex]) : priority list)
     ((l3 [@ex]) : priority list) ((l23 [@ex]) : priority list)
     ((l123 [@ex]) : priority list) ->
  list_len lemp == 0
  && hd l3 e3 && tl l3 lemp && hd l23 e2 && tl l23 l3 && hd l123 e1
  && tl l123 l23 && is_high e1 && is_medium e2 && is_low e3 e3list
  && list_len e3list == 0
  && list_mem l123 e1 && list_mem l123 e2 && list_mem l123 e3

let[@axiom] wf_priority =
 fun (v : priority) ->
  implies (wf_priority v)
    (is_high v
    || is_medium v && fun ((wl [@ex]) : (int * int) list) ->
       rational_zero_one_list wl && list_len wl <= 100 && is_low v wl)

(* let[@axiom] wf_priority_2 = *)
(*  fun (v : priority) -> *)
(*   implies (wf_priority v) (fun ((x_17 [@ex]) : priority list) -> *)
(*       list_len x_17 == 0 && fun ((x_18 [@ex]) : (int * int) list) -> *)
(*       list_len x_18 == 0 && fun ((x_19 [@ex]) : priority) -> *)
(*       is_low x_19 x_18 && fun ((x_20 [@ex]) : priority list) -> *)
(*       hd x_20 x_19 && tl x_20 x_17 *)
(*       && fun ((x_21 [@ex]) : priority) -> *)
(*       is_medium x_21 && fun ((x_22 [@ex]) : priority list) -> *)
(*       hd x_22 x_21 && tl x_22 x_20 *)
(*       && fun ((x_23 [@ex]) : priority) -> *)
(*       is_high x_23 && fun ((x_24 [@ex]) : priority list) -> *)
(*       hd x_24 x_23 && tl x_24 x_22 *)
(*       && fun ((x_44 [@ex]) : priority) -> *)
(*       list_mem x_24 x_44 *)
(*       && ((is_high x_44 && is_high v) *)
(*          || (is_medium x_44 && is_medium v) *)
(*             && fun ((lowl [@ex]) : (int * int) list) -> *)
(*             is_low x_44 lowl && fun ((x_50 [@ex]) : (int * int) list) -> *)
(*             rational_zero_one_list x_50 && list_len x_50 <= 100 && is_low v x_50 *)
(*          )) *)

(** Tezos *)

let[@axiom] tl_wf_decreasing =
 fun (l : 'a list) (ll : 'a list) -> (tl l ll)#==>(decreasing ll l)

let[@axiom] list_concat_wf_decreasing =
 fun (l : 'a list) (l1 : 'a list) (l2 : 'a list) ->
  (list_concat l1 l2 l)#==>(decreasing l1 l && decreasing l2 l)

let[@axiom] l2t_pre_singleton =
 fun (l : 'a list) (x : 'a) (xs : 'a list) (tr : 'a tezosTree) ->
  (l2t_pre l tr && hd l x && tl l xs)#==>(iff
                                            (list_len xs == 0)
                                            (tezos_leaf tr x))

(* let[@axiom] tezos = *)
(*  fun (blocks : 'a list) -> *)
(*   fun (v : 'a tezosTree) -> *)
(*    implies (l2t_pre blocks v) (fun ((x [@ex]) : 'a) -> *)
(*        fun ((xs [@ex]) : 'a list) -> *)
(*         hd blocks x && tl blocks xs *)
(*         && (list_len xs == 0 *)
(*            || (fun ((x_127 [@ex]) : 'a tezosTree) -> *)
(*                 l2t_pre xs x_127 && tezos_node1 v x x_127) *)
(*               && fun ((x_130 [@ex]) : int) -> *)
(*               0 <= x_130 *)
(*               && x_130 <= list_len xs *)
(*               && fun ((x_131 [@ex]) : 'a list * 'a list) -> *)
(*               list_concat (fst x_131) (snd x_131) xs *)
(*               && ( list_len (fst x_131) == 0 *)
(*                  && ( (list_len (snd x_131) == 0 && tezos_leaf v x) *)
(*                     || fun ((x_133 [@ex]) : 'a tezosTree) -> *)
(*                       l2t_pre (snd x_131) x_133 && tezos_node1 v x x_133 ) *)
(*                  || fun ((x_132 [@ex]) : 'a tezosTree) -> *)
(*                    l2t_pre (fst x_131) x_132 *)
(*                    && ( (list_len (snd x_131) == 0 && tezos_node1 v x x_132) *)
(*                       || fun ((x_134 [@ex]) : 'a tezosTree) -> *)
(*                         l2t_pre (snd x_131) x_134 && tezos_node2 v x x_132 x_134 *)
(*                       ) ))) *)

(** String *)

let[@axiom] string_len_geq_zero = fun (l : string) -> string_len l >= 0

(** List *)

let[@axiom] list_mem_has_nth =
 fun (l : 'a list) (v : 'a) ->
  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->
  0 <= idx && idx < list_len l && list_nth_pred l idx v)

let[@axiom] list_snd_mem_none_when_len_0 =
 fun (l : (int * 'a) list) (v : 'a) ->
  (list_len l == 0)#==>(not (list_snd_mem l v))

let[@axiom] list_snd_mem_implies_len_gt_zero =
 fun (l : (int * 'a) list) (v : 'a) -> (list_snd_mem l v)#==>(list_len l > 0)

let[@axiom] list_len_gt_zero_implies_has_hd_tl =
 fun (l : 'a list) ->
  (list_len l > 0) #==> (fun ((hde [@ex]) : 'a) ((tle [@ex]) : 'a list) ->
  hd l hde && tl l tle)

let[@axiom] list_snd_mem_implies_snd_mem_hd_or_tl =
 fun (l : (int * 'a) list) (v : 'a) (hde : int * 'a) (tle : (int * 'a) list) ->
  (list_snd_mem l v && hd l hde && tl l tle)#==>(v == snd hde
                                                || list_snd_mem tle v)

let[@axiom] list_tl_len_minus_one =
 fun (l : 'a list) (tle : 'a list) ->
  (tl l tle)#==>(list_len l == 1 + list_len tle)

let[@axiom] list_hd_implies_len_gt_zero =
 fun (l : 'a list) (v : 'a) -> (hd l v)#==>(list_len l > 0)

let[@axiom] list_tl_implies_len_gt_zero =
 fun (l : 'a list) (tle : 'a list) -> (tl l tle)#==>(list_len l > 0)

let[@axiom] list_hd_is_mem =
 fun (l : 'a list) (v : 'a) -> (hd l v)#==>(list_mem l v)

let[@axiom] list_hd_unique =
 fun (l : 'a list) (x : 'a) (y : 'a) -> (hd l x && hd l y)#==>(x == y)

let[@axiom] list_tl_unique =
 fun (l : 'a list) (tle1 : 'a list) (tle2 : 'a list) ->
  (tl l tle1 && tl l tle2)#==>(tle1 == tle2)

let[@axiom] list_len_geq_zero = fun (l : 'a list) -> list_len l >= 0

(* let[@axiom] list_len_geq_zero_implies_list_ex = *)
(*  fun (n : int) -> (0 <= n) #==> (fun ((l [@ex]) : 'a list) -> list_len l == n) *)

let[@axiom] int_list_ex_0_9 =
 fun ((l0 [@ex]) : int list) ((l1 [@ex]) : int list) ((l2 [@ex]) : int list) ->
  tl l2 l1 && tl l1 l0 && list_len l0 == 0 && hd l1 1 && hd l2 9

(** List :: uniq *)

let[@axiom] unique_list_implies_hd_not_mem_in_tl =
 fun (l : int list) (x : int) (xs : int list) ->
  (uniq l && hd l x && tl l xs)#==>(uniq xs && not (list_mem xs x))

let[@axiom] unique_list_length_1_ex =
 fun ((l [@ex]) : int list) -> list_len l == 1 && uniq l

(** List :: sorted *)

let[@axiom] list_emp_sorted (l : int list) = (list_len l == 0)#==>(sorted l)

let[@axiom] list_tl_sorted (l : int list) (l1 : int list) =
  (tl l l1 && sorted l)#==>(sorted l1)

let[@axiom] list_hd_sorted (l : int list) (l1 : int list) (x : int) (y : int) =
  (tl l l1 && sorted l)#==>(list_len l1 == 0
                           || ((hd l1 y && hd l x)#==>(x <= y)))

(** List :: mem *)

let[@axiom] list_mem_destruct =
 fun (v : 'a list) (h : 'a) (l : 'a list) (x : 'a) ->
  implies (hd v h && tl v l) (iff (list_mem v x) (h == x || list_mem l x))

(** Tree *)

let[@axiom] tree_leaf_no_root (l : int tree) (x : int) =
  (depth l == 0)#==>(not (root l x))

let[@axiom] tree_leaf_no_ch (l : int tree) (l1 : int tree) =
  (depth l == 0)#==>(not (lch l l1 || rch l l1))

let[@axiom] tree_no_leaf_ex_lch (l : int tree) ((l1 [@ex]) : int tree) =
  (not (depth l == 0))#==>(lch l l1)

let[@axiom] tree_no_leaf_ex_rch (l : int tree) ((l2 [@ex]) : int tree) =
  (not (depth l == 0))#==>(rch l l2)

let[@axiom] tree_no_leaf_ex_root (l : int tree) ((x [@ex]) : int) =
  (not (depth l == 0))#==>(root l x)

let[@axiom] tree_root_no_leaf (l : int tree) (x : int) =
  (root l x)#==>(not (depth l == 0))

let[@axiom] tree_ch_no_leaf (l : int tree) (l1 : int tree) =
  (lch l l1 || rch l l1)#==>(not (depth l == 0))

let[@axiom] tree_depth_geq_0 (l : int tree) (n : int) =
  (depth l == n)#==>(n >= 0)

let[@axiom] tree_ch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 || rch l l1)#==>(depth l1 <= depth l - 1)

(** tree_mem *)

let[@axiom] tree_root_mem (l : int tree) (x : int) =
  (root l x)#==>(tree_mem l x)

let[@axiom] tree_mem_lch_mem (l : int tree) (l1 : int tree) (x : int) =
  (lch l l1 && tree_mem l1 x)#==>(tree_mem l x)

let[@axiom] tree_mem_rch_mem (l : int tree) (l1 : int tree) (x : int) =
  (rch l l1 && tree_mem l1 x)#==>(tree_mem l x)

(** bst *)

let[@axiom] tree_leaf_bst (l : int tree) = (depth l == 0)#==>(bst l)

let[@axiom] tree_bst_lch_bst (l : int tree) (l1 : int tree) =
  (lch l l1 && bst l)#==>(bst l1)

let[@axiom] tree_bst_rch_bst (l : int tree) (l1 : int tree) =
  (rch l l1 && bst l)#==>(bst l1)

let[@axiom] tree_bst_lch_mem_lt_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && lch l l1 && root l x && tree_mem l1 y)#==>(y < x)

let[@axiom] tree_bst_rch_mem_gt_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && rch l l1 && root l x && tree_mem l1 y)#==>(x < y)

(* let[@axiom] list_emp_unique = *)
(*  fun (l : int list) -> (list_len l == 0)#==>(uniq l) *)

(* let[@axiom] unique_list_tl_unique_list = *)
(*  fun (l : int list) (l1 : int list) -> (tl l l1 && uniq l)#==>(uniq l1) *)

(* let[@axiom] unique_list_hd_not_mem = *)
(*  fun (l : int list) (l1 : int list) (x : int) -> *)
(*   (tl l l1 && uniq l && hd l1 x)#==>(not (list_mem l1 x)) *)

(** tree :: complete *)

let[@axiom] tree_complete_lch_complete (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l)#==>(complete l1)

let[@axiom] tree_complete_rch_complete (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l)#==>(complete l1)

let[@axiom] tree_complete_lch_depth_minus_1 (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l)#==>(depth l == depth l1 + 1)

let[@axiom] tree_complete_rch_depth_minus_1 (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l)#==>(depth l == depth l1 + 1)

(** tree :: heap *)

let[@axiom] tree_heap_lch_heap (l : int tree) (l1 : int tree) =
  (lch l l1 && heap l)#==>(heap l1)

let[@axiom] tree_heap_rch_heap (l : int tree) (l1 : int tree) =
  (rch l l1 && heap l)#==>(heap l1)

let[@axiom] tree_heap_root_lt_lch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && lch l l1 && root l x && root l1 y)#==>(y < x)

let[@axiom] tree_heap_root_rt_rch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && rch l l1 && root l x && root l1 y)#==>(y < x)

(** stream *)

let[@axiom] stream_stream_emp_no_stream_hd (l : int stream) (x : int) =
  (stream_len l == 0)#==>(not (stream_hd l x))

let[@axiom] stream_stream_emp_no_stream_tl (l : int stream)
    (l1 : int stream lazyty) =
  (stream_len l == 0)#==>(not (stream_tl l (forc l1)))

let[@axiom] stream_no_stream_emp_ex_stream_tl (l : int stream)
    ((l1 [@ex]) : int stream lazyty) =
  (not (stream_len l == 0))#==>(stream_tl l (forc l1))

let[@axiom] stream_no_stream_emp_ex_stream_hd (l : int stream) ((x [@ex]) : int)
    =
  (not (stream_len l == 0))#==>(stream_hd l x)

let[@axiom] stream_stream_hd_no_stream_emp (l : int stream) (x : int) =
  (stream_hd l x)#==>(not (stream_len l == 0))

let[@axiom] stream_stream_tl_no_stream_emp (l : int stream)
    (l1 : int stream lazyty) =
  (stream_tl l (forc l1))#==>(not (stream_len l == 0))

let[@axiom] stream_stream_len_geq_0 (l : int stream) = stream_len l >= 0

let[@axiom] stream_stream_tl_stream_len_plus_1 (l : int stream)
    (l1 : int stream) =
  (stream_tl l l1)#==>(stream_len l1 + 1 == stream_len l)

(** leafisthp *)

(** basic *)

let[@axiom] leftisthp_leftisthp_leaf_no_leftisthp_root (l : int leftisthp)
    (x : int) =
  (leftisthp_depth l == 0)#==>(not (leftisthp_root l x))

let[@axiom] leftisthp_leftisthp_leaf_no_ch (l : int leftisthp)
    (l1 : int leftisthp) =
  (leftisthp_depth l == 0)#==>(not (leftisthp_lch l l1 || leftisthp_rch l l1))

let[@axiom] leftisthp_leftisthp_leaf_no_rank (l : int leftisthp) (r : int) =
  (leftisthp_depth l == 0)#==>(not (leftisthp_rank l r))

let[@axiom] leftisthp_no_leftisthp_leaf_ex_leftisthp =
 fun (v : int leftisthp) ->
  (leftisthp_depth v > 0)
  #==>
  (fun ((lt [@ex]) : int leftisthp)
    ((r [@ex]) : int)
    ((_x_3 [@ex]) : int)
    ((rt [@ex]) : int leftisthp)
  ->
  leftisthp_lch v lt && leftisthp_rank v r && leftisthp_rch v rt
  && leftisthp_root v _x_3)

let[@axiom] leftisthp_leftisthp_root_no_leftisthp_leaf (l : int leftisthp)
    (x : int) =
  (leftisthp_root l x)#==>(not (leftisthp_depth l == 0))

let[@axiom] leftisthp_ch_no_leftisthp_leaf (l : int leftisthp)
    (l1 : int leftisthp) =
  (leftisthp_lch l l1 || leftisthp_rch l l1)#==>(not (leftisthp_depth l == 0))

let[@axiom] leftisthp_right_depth_leq_depth (l : int leftisthp) (r : int) =
  (leftisthp_rank l r)#==>(r <= leftisthp_depth l && 0 < r)

let[@axiom] leftisthp_right_depth_m1_depth (l : int leftisthp)
    (l1 : int leftisthp) (r : int) =
  (leftisthp_rch l l1 && leftisthp_rank l r)#==>(leftisthp_depth l1 == r - 1)

let[@axiom] leftisthp_leftisthp_depth_ch_leftisthp_depth_minus_1
    (tr : int leftisthp) (tr1 : int leftisthp) (n : int) =
  (leftisthp_lch tr tr1)#==>(leftisthp_depth tr == leftisthp_depth tr1 + 1)

let[@axiom] leftisthp_leftisthp_depth_geq_0 (l : int leftisthp) =
  leftisthp_depth l >= 0

(** rbtree *)

let[@axiom] rbtree_rb_leaf_no_rb_root (l : int rbtree) (x : int) =
  (rb_leaf l)#==>(not (rb_root l x))

let[@axiom] rbtree_rb_leaf_no_rb_root_color (l : int rbtree) (x : bool) =
  (rb_leaf l)#==>(not (rb_root_color l x))

let[@axiom] rbtree_rb_leaf_no_ch (l : int rbtree) (l1 : int rbtree) =
  (rb_leaf l)#==>(not (rb_lch l l1 || rb_rch l l1))

let[@axiom] rbtree_no_rb_leaf_ex_ch (l : int rbtree) ((l1 [@ex]) : int rbtree)
    ((l2 [@ex]) : int rbtree) =
  (not (rb_leaf l))#==>(rb_lch l l1 && rb_rch l l2)

let[@axiom] rbtree_no_rb_leaf_ex_rb_root (l : int rbtree) ((x [@ex]) : int) =
  (not (rb_leaf l))#==>(rb_root l x)

let[@axiom] rbtree_no_rb_leaf_ex_rb_root_color (l : int rbtree)
    ((x [@ex]) : bool) =
  (not (rb_leaf l))#==>(rb_root_color l x)

let[@axiom] rbtree_rb_root_no_rb_leaf (l : int rbtree) (x : int) =
  (rb_root l x)#==>(not (rb_leaf l))

let[@axiom] rbtree_rb_root_color_no_rb_leaf (l : int rbtree) (x : bool) =
  (rb_root_color l x)#==>(not (rb_leaf l))

(* let[@axiom] rbtree_ch_no_rb_leaf (l : int rbtree) (l1 : int rbtree) = *)
(*   (rb_lch l l1 || rb_rch l l1)#==>(not (rb_leaf l)) *)

let[@axiom] rbtree_num_black_0_rb_leaf (l : int rbtree) =
  (num_black l == 0 && not (rb_root_color l true))#==>(rb_leaf l)

(* let[@axiom] rbtree_num_black_geq_0 (l : int rbtree) = num_black l >= 0 *)

let[@axiom] rbtree_rb_leaf_num_black_0 (l : int rbtree) (n : int) =
  (rb_leaf l && num_black l == n)#==>(n == 0)

(* let[@axiom] rbtree_positive_num_black_is_not_rb_leaf (l : int rbtree) = *)
(*   (num_black l > 0)#==>(not (rb_leaf l)) *)

let[@axiom] num_black_root_black_lt_minus_1 (v : int rbtree) (lt : int rbtree) =
  (rb_root_color v false && rb_lch v lt)#==>(1 + num_black lt == num_black v)

let[@axiom] num_black_root_black_rt_minus_1 (v : int rbtree) (rt : int rbtree) =
  (rb_root_color v false && rb_rch v rt)#==>(1 + num_black rt == num_black v)

let[@axiom] num_black_root_red_lt_same (v : int rbtree) (lt : int rbtree) =
  (rb_root_color v true && rb_lch v lt)#==>(num_black lt == num_black v)

let[@axiom] num_black_root_red_rt_same (v : int rbtree) (rt : int rbtree) =
  (rb_root_color v true && rb_rch v rt)#==>(num_black rt == num_black v)

(* let[@axiom] num_black_root_black_0_lt_leaf (v : int rbtree) (lt : int rbtree) = *)
(*   (num_black v == 0 && rb_lch v lt)#==>(rb_leaf lt) *)

(* let[@axiom] num_black_root_black_0_rt_leaf (v : int rbtree) (rt : int rbtree) = *)
(*   (num_black v == 0 && rb_rch v rt)#==>(rb_leaf rt) *)

(* let[@axiom] num_black_root_black_0_rt_red (v : int rbtree) (rt : int rbtree) = *)
(*   (num_black v == 0 && rb_rch v rt)#==>(rb_root_color v true) *)

let[@axiom] no_red_red_lt (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt)#==>(no_red_red lt)

let[@axiom] no_red_red_rt (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt)#==>(no_red_red rt)

let[@axiom] no_red_red_root_red_lt_not_red (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt && rb_root_color v true)#==>(not
                                                              (rb_root_color lt
                                                                 true))

let[@axiom] no_red_red_root_red_rt_not_red (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt && rb_root_color v true)#==>(not
                                                              (rb_root_color rt
                                                                 true))

(* let[@axiom] black_lt_black_num_black_gt_1 (v : int rbtree) (lt : int rbtree) = *)
(*   (rb_lch v lt && rb_root_color v false && rb_root_color lt false)#==>(num_black *)
(*                                                                          v > 1) *)

(* let[@axiom] black_rt_black_num_black_gt_1 (v : int rbtree) (rt : int rbtree) = *)
(*   (rb_rch v rt && rb_root_color v false && rb_root_color rt false)#==>(num_black *)
(*                                                                          v > 1) *)

(** stlc *)

let[@axiom] type_eq_0 =
 fun (tau_a : stlc_ty) ->
  fun (tau_b : stlc_ty) ->
   implies (num_arr tau_a == 0) (iff (tau_a == tau_b) (num_arr tau_b == 0))

let[@axiom] type_eq_geq_0 =
 fun (tau_a : stlc_ty) ->
  fun (tau_b : stlc_ty) ->
   fun (tau_a_1 : stlc_ty) ->
    fun (tau_b_3 : stlc_ty) ->
     fun (tau_a_2 : stlc_ty) ->
      fun (tau_b_4 : stlc_ty) ->
       implies
         (stlc_ty_arr1 tau_a tau_a_1 && stlc_ty_arr2 tau_a tau_a_2
        && stlc_ty_arr1 tau_b tau_b_3 && stlc_ty_arr2 tau_b tau_b_4)
         (iff (tau_a == tau_b) (tau_a_1 == tau_b_3 && tau_a_2 == tau_b_4))

let[@axiom] stlc_const_gen =
 fun (v : stlc_term) ->
  (is_const v) #==> (fun ((n2 [@ex]) : int) -> 0 <= n2 && stlc_const v n2)

let[@axiom] stlc_ty_num_arr_ge_0 = fun (v : stlc_ty) -> num_arr v >= 0

let[@axiom] stlc_ty_num_arr_gt_0_arr1_arr2 =
 fun (v : stlc_ty) ->
  (num_arr v > 0) #==> (fun ((t1 [@ex]) : stlc_ty) ((t2 [@ex]) : stlc_ty) ->
  stlc_ty_arr1 v t1 && stlc_ty_arr2 v t2)

let[@axiom] stlc_ty_num_arr_arr_sum =
 fun (v : stlc_ty) (t1 : stlc_ty) (t2 : stlc_ty) ->
  (stlc_ty_arr1 v t1 && stlc_ty_arr2 v t2)#==>(num_arr v
                                              == 1 + num_arr t1 + num_arr t2)

let[@axiom] list_index_list_len_gt_0 =
 fun (gamma : stlc_ty list) (tau : stlc_ty) (i : int) ->
  (list_index gamma i tau)#==>(0 <= i && i < list_len gamma)

let[@axiom] list_index_hd_or_tl_minus_1 =
 fun (gamma : stlc_ty list) (tau : stlc_ty) (v : int) (tau_hd : stlc_ty)
     (gamma_rest : stlc_ty list) ->
  implies
    (hd gamma tau_hd && tl gamma gamma_rest && list_index gamma v tau)
    ((v > 0 && list_index gamma_rest (v - 1) tau) || (v == 0 && tau_hd == tau))

let[@axiom] stlc_var_typing =
 fun (gamma : stlc_ty list) (tau : stlc_ty) (v : stlc_term) ->
  implies
    (typing gamma v tau && is_var v)
    (fun ((id [@ex]) : int) -> list_index gamma id tau && stlc_id v id)

let[@axiom] stlc_var_typing_another =
 fun (gamma : stlc_ty list) ->
  fun (tau : stlc_ty) ->
   fun (v : stlc_term) ->
    implies
      (typing gamma v tau && is_var v)
      (fun ((rev_id [@ex]) : int) ->
        list_index gamma (list_len gamma - rev_id) tau
        && stlc_id v (list_len gamma - rev_id))

let[@axiom] stlc_ty_arr1_wf_decreasing =
 fun (v : stlc_ty) (t1 : stlc_ty) -> (stlc_ty_arr1 v t1)#==>(decreasing t1 v)

let[@axiom] stlc_ty_arr2_wf_decreasing =
 fun (v : stlc_ty) (t2 : stlc_ty) -> (stlc_ty_arr2 v t2)#==>(decreasing t2 v)

let[@axiom] stlc_typing_no_app_no_arr_is_const_var =
 fun (tau : stlc_ty) (gamma : stlc_ty list) (v : stlc_term) ->
  (typing gamma v tau && num_arr tau == 0)#==>(is_const v || is_var v)

let[@axiom] stlc_typing_no_app_no_arr_is_abs_app =
 fun (v : stlc_term) -> (num_app v > 0)#==>(is_abs v || is_app v)

let[@axiom] stlc_typing_abs_app_exclusive =
 fun (v : stlc_term) -> not (is_abs v && is_app v)

let[@axiom] stlc_typing_no_app_abs =
 fun (tau : stlc_ty) (gamma : stlc_ty list) (v : stlc_term) (tau1_1 : stlc_ty)
     (tau2_1 : stlc_ty) ->
  implies
    (typing gamma v tau
    && num_app v == 0
    && num_arr tau > 0
    && stlc_ty_arr1 tau tau1_1 && stlc_ty_arr2 tau tau2_1)
    (fun ((_x_31 [@ex]) : stlc_ty list) ->
      hd _x_31 tau1_1 && tl _x_31 gamma
      && fun ((_x_32 [@ex]) : stlc_term) ->
      decreasing tau2_1 tau && typing _x_31 _x_32 tau2_1
      && num_app _x_32 == 0
      && stlc_abs_ty v tau1_1 && stlc_abs_body v _x_32)

let[@axiom] stlc_meaure_num_geq_0 =
 fun (num : int) (tau : stlc_ty) (v : int) ->
  (stlc_measure tau num v)#==>(num >= 0)

let[@axiom] stlc_meaure_num_decr =
 fun (num : int) (tau : stlc_ty) (v : int) (num1 : int) (tau1 : stlc_ty)
     (v1 : int) ->
  implies
    (stlc_measure tau num v && stlc_measure tau1 num1 v1 && num1 < num)
    (v1 < v)

let[@axiom] stlc_meaure_tau_arr2 =
 fun (num : int) (tau : stlc_ty) (v : int) (tau1 : stlc_ty) (v1 : int) ->
  implies
    (stlc_measure tau num v && stlc_measure tau1 num v1 && stlc_ty_arr2 tau tau1)
    (v1 < v)

let[@axiom] stlc_app1_num_app_lt =
 fun (func : stlc_term) (v : stlc_term) ->
  (stlc_app1 v func)#==>(num_app func < num_app v)

let[@axiom] stlc_app1_num_app_lt_arg =
 fun (func : stlc_term) (v : stlc_term) (arg : stlc_term) ->
  (stlc_app1 v func && stlc_app2 v arg)#==>(num_app arg
                                           < num_app v - num_app func)

let[@axiom] stlc_typing_app_func_typing =
 fun (func_ty : stlc_ty) (arg_ty : stlc_ty) (tau : stlc_ty)
     (gamma : stlc_ty list) (func : stlc_term) (v : stlc_term)
     (arg : stlc_term) ->
  implies
    (stlc_ty_arr1 func_ty arg_ty
    && stlc_ty_arr2 func_ty tau && stlc_app1 v func && stlc_app2 v arg
    && typing gamma v tau && typing gamma func func_ty)
    (typing gamma arg arg_ty)

let[@axiom] stlc_typing_abs_typing =
 fun (func_ty : stlc_ty) (arg_ty : stlc_ty) (tau : stlc_ty)
     (gamma : stlc_ty list) (body : stlc_term) (v : stlc_term) (arg : stlc_term)
     (gamma' : stlc_ty list) ->
  implies
    (stlc_ty_arr1 func_ty arg_ty
    && stlc_ty_arr2 func_ty tau && stlc_abs_ty v arg_ty && stlc_abs_body v body
    && typing gamma v func_ty && hd gamma' arg_ty && tl gamma' gamma)
    (typing gamma' body tau)

let[@axiom] stlc_typing =
 fun (measure : int) ->
  fun (num : int) ->
   fun (tau : stlc_ty) (gamma : stlc_ty list) (v : stlc_term) ->
    implies
      (stlc_measure tau num measure
      && typing gamma v tau
      && num_app v == num
      && num > 0)
      ( (fun ((func [@ex]) : stlc_term)
          ((arg [@ex]) : stlc_term)
          ((arg_ty [@ex]) : stlc_ty)
          ((func_ty [@ex]) : stlc_ty)
          ((m2 [@ex]) : int)
          ((m1 [@ex]) : int)
        ->
          stlc_ty_arr1 func_ty arg_ty
          && stlc_ty_arr2 func_ty tau && stlc_app1 v func && stlc_app2 v arg
          && typing gamma func func_ty
          && stlc_measure arg_ty (num_app arg) m2
          && stlc_measure func_ty (num_app func) m1)
      ||
      fun ((tau1_4 [@ex]) : stlc_ty)
        ((tau2_4 [@ex]) : stlc_ty)
        ((_x_48 [@ex]) : stlc_ty list)
        ((body_2 [@ex]) : stlc_term)
        ((m3_0 [@ex]) : int)
      ->
        stlc_ty_arr1 tau tau1_4 && stlc_ty_arr2 tau tau2_4
        && stlc_measure tau2_4 num m3_0
        && hd _x_48 tau1_4 && tl _x_48 gamma
        && num_app body_2 == num
        && stlc_abs_ty v tau1_4 && stlc_abs_body v body_2 )

(** Xen Api *)

let[@axiom] wf_file_kind_list_6_ex =
 fun (v : int) ->
  implies (wf_file_kind v) (fun ((_x [@ex]) : int list) ->
      list_len _x == 0 && fun ((_x_0 [@ex]) : int list) ->
      hd _x_0 6 && tl _x_0 _x
      && fun ((_x_1 [@ex]) : int list) ->
      hd _x_1 5 && tl _x_1 _x_0
      && fun ((_x_2 [@ex]) : int list) ->
      hd _x_2 4 && tl _x_2 _x_1
      && fun ((_x_3 [@ex]) : int list) ->
      hd _x_3 3 && tl _x_3 _x_2
      && fun ((_x_4 [@ex]) : int list) ->
      hd _x_4 2 && tl _x_4 _x_3
      && fun ((_x_5 [@ex]) : int list) ->
      hd _x_5 1 && tl _x_5 _x_4
      && fun ((_x_6 [@ex]) : int list) ->
      hd _x_6 0 && tl _x_6 _x_5 && list_mem _x_6 v)

let[@axiom] wf_timeout =
 fun (v : float) ->
  implies (wf_timeouts v) (fun ((_x [@ex]) : float list) ->
      list_len _x == 0 && fun ((_x_0 [@ex]) : float list) ->
      hd _x_0 0.3 && tl _x_0 _x
      && fun ((_x_1 [@ex]) : float list) ->
      hd _x_1 0.1 && tl _x_1 _x_0
      && fun ((_x_2 [@ex]) : float list) ->
      hd _x_2 0.001 && tl _x_2 _x_1
      && fun ((_x_3 [@ex]) : float list) ->
      hd _x_3 0. && tl _x_3 _x_2 && list_mem _x_3 v)

let[@axiom] wf_total_delay =
 fun (v : float) ->
  implies (wf_total_delay v) (fun ((_x [@ex]) : float list) ->
      list_len _x == 0 && fun ((_x_0 [@ex]) : float list) ->
      hd _x_0 0.4 && tl _x_0 _x
      && fun ((_x_1 [@ex]) : float list) ->
      hd _x_1 0.1 && tl _x_1 _x_0
      && fun ((_x_2 [@ex]) : float list) ->
      hd _x_2 0.01 && tl _x_2 _x_1
      && fun ((_x_3 [@ex]) : float list) ->
      hd _x_3 0.001 && tl _x_3 _x_2 && list_mem _x_3 v)

let[@axiom] wf_size_bound =
 fun (v : int) ->
  implies (wf_size_bound v) (fun ((_x_9 [@ex]) : (int * int) list) ->
      list_len _x_9 == 0 && fun ((_x_10 [@ex]) : (int * int) list) ->
      hd _x_10 (1, 100)
      && tl _x_10 _x_9
      && fun ((_x_11 [@ex]) : (int * int) list) ->
      hd _x_11 (2, 10)
      && tl _x_11 _x_10
      && fun ((_x_12 [@ex]) : (int * int) list) ->
      hd _x_12 (4, 2)
      && tl _x_12 _x_11
      && fun ((_x_13 [@ex]) : (int * int) list) ->
      hd _x_13 (4, 0) && tl _x_13 _x_12 && list_snd_mem _x_13 v)

let[@axiom] wf_size_bound_geq_0 = fun (v : int) -> (wf_size_bound v)#==>(v >= 0)

let[@axiom] is_testable_kind =
 fun (v : int) -> (is_testable_kind v)#==>(wf_file_kind v)

let[@axiom] wf_select_fd_spec =
 fun (v : select_fd_spec) ->
  implies (wf_select_fd_spec v)
    ( is_testable_kind v.kind && fun ((x_wait [@ex]) : float) ->
      wf_timeouts x_wait
      && ((has_immediate_timeout v.kind && v.wait == 0.)
         || ((not (has_immediate_timeout v.kind)) && v.wait == x_wait)) )

let[@axiom] wf_select_fd_spec_list =
 fun (v : select_fd_spec list) ->
  (wf_select_fd_spec_list v) #==> (fun ((x_33 [@ex]) : int) ->
  wf_size_bound x_33 && list_len v <= x_33)

(* let[@axiom] wf_fd_size = *)
(*  fun (v : int) -> *)
(*   implies (wf_fd_size v) *)
(*     (fun *)
(*       ((_x [@ex]) : int list) *)
(*       ((_x_4 [@ex]) : int list) *)
(*       ((_x_7 [@ex]) : int list) *)
(*       ((_x_10 [@ex]) : int list) *)
(*       ((_x_11 [@ex]) : int list) *)
(*       ((_x_14 [@ex]) : int list) *)
(*       ((_x_15 [@ex]) : int list) *)
(*       ((_x_16 [@ex]) : int list) *)
(*       ((_x_17 [@ex]) : int list) *)
(*       ((_x_18 [@ex]) : int list) *)
(*     -> *)
(*       list_len _x == 0 *)
(*       && hd _x_4 655363 && tl _x_4 _x && hd _x_7 131072 && tl _x_7 _x_4 *)
(*       && hd _x_10 65537 && tl _x_10 _x_7 && hd _x_11 65536 && tl _x_11 _x_10 *)
(*       && hd _x_14 65535 && tl _x_14 _x_11 && hd _x_15 4096 && tl _x_15 _x_14 *)
(*       && hd _x_16 100 && tl _x_16 _x_15 && hd _x_17 1 && tl _x_17 _x_16 *)
(*       && hd _x_18 0 && tl _x_18 _x_17 && list_mem _x_18 v) *)

let[@axiom] wf_fd =
 fun (v : fd) ->
  implies (wf_fd v) (fun ((total_delay [@ex]) : float) ((x_56 [@ex]) : int) ->
      wf_total_delay total_delay && wf_fd_size x_56 && is_testable_kind v.kind
      && v.delay_write == v.delay_read
      && (v.kind == 0
          && wf_delay_size v.delay_read total_delay 512
          && v.kind == v.kind && v.size == 512
         || (not (v.kind == 0))
            && wf_delay_size v.delay_read total_delay x_56
            && v.kind == v.kind && v.size == x_56))

(** VeLLVM *)

(* let[@axiom] llvm_int_size_implies_content = *)
(*  fun (v : dvalue) (s : int) -> *)
(*   (dvalue_int_size v s)#==>( 0 <= s && fun ((y [@ex]) : int) -> *)
(*                              0 <= y && y < 2 ^ s && dvalue_int_content v y ) *)

let[@axiom] llvm_int_content_limit =
 fun (v : dvalue) (y : int) -> (dvalue_int_content v y)#==>(0 <= y && y <= 10000)

let[@axiom] llvm_typ_vector_decreasing =
 fun (v : typ) (t2 : typ) -> (type_vector2 v t2)#==>(decreasing t2 v)

let[@axiom] llvm_typ_array_decreasing =
 fun (v : typ) (t2 : typ) -> (type_array2 v t2)#==>(decreasing t2 v)

let[@axiom] llvm_typing_int =
 fun (t : typ) (v : dvalue) (i : int) ->
  (llvm_typing v t && type_i t i)#==>(dvalue_int_size v i
                                     && (i == 1 || i == 8 || i == 32 || i == 64)
                                     )

let[@axiom] llvm_typing_none =
 fun (t : typ) (v : dvalue) ->
  (llvm_typing v t && type_void t)#==>(dvalue_none v)

let[@axiom] llvm_typing_vector =
 fun (t : typ) (v : dvalue) (sz : int) (ty : typ) ->
  (llvm_typing v t && type_vector1 t sz && type_vector2 t ty)
  #==> (fun ((dvec [@ex]) : dvalue) ->
  llvm_typing dvec ty && fun ((x_22 [@ex]) : dvalue list) ->
  dvalue_list x_22 dvec
  && list_len x_22 == sz
  && dvalue_vector_typ v t
  && dvalue_vector_content v x_22)

let[@axiom] llvm_typing_array =
 fun (t : typ) (v : dvalue) (sz' : int) (ty' : typ) ->
  (llvm_typing v t && type_array1 t sz' && type_array2 t ty')
  #==> (fun ((darr [@ex]) : dvalue) ->
  llvm_typing darr ty' && fun ((x_29 [@ex]) : dvalue list) ->
  dvalue_list x_29 darr
  && list_len x_29 == sz'
  && dvalue_array_typ v t
  && dvalue_array_content v x_29)

let[@axiom] llvm_typing_others =
 fun (t : typ) (v : dvalue) -> not (llvm_typing v t && type_others t)

let[@axiom] llvm_typ_destruct =
 fun (t : typ) (v : dvalue) ->
  implies (llvm_typing v t)
    ((fun ((i [@ex]) : int) -> type_i t i)
    || type_void t
    || (fun ((sz [@ex]) : int) ((ty [@ex]) : typ) ->
      type_vector1 t sz && type_vector2 t ty)
    || fun ((sz' [@ex]) : int) ->
    fun ((ty' [@ex]) : typ) -> type_array1 t sz' && type_array2 t ty')

let[@axiom] llvm_typ_destruct2 =
 fun (t : typ) ->
  fun (v : dvalue) ->
   implies (llvm_typing v t) (fun ((i [@exists]) : int) ->
       type_i t i && dvalue_int_size v i
       && (( i == 1 && fun ((_x_1 [@exists]) : bool list) ->
             list_len _x_1 == 0 && fun ((_x_2 [@exists]) : bool list) ->
             hd _x_2 false && tl _x_2 _x_1
             && fun ((_x_3 [@exists]) : bool list) ->
             hd _x_3 true && tl _x_3 _x_2
             && (list_mem _x_3 true && dvalue_int_size v 1
                 && dvalue_int_content v 1
                || list_mem _x_3 false && dvalue_int_size v 1
                   && dvalue_int_content v 0) )
          || (i == 8 && dvalue_int_size v 8
             && fun ((x_8 [@exists]) : int) -> dvalue_int_content v x_8)
          || ( i == 32 && fun ((x_12 [@exists]) : int) ->
               dvalue_int_content v x_12 )
          || i == 64 && fun ((x_16 [@exists]) : int) ->
             dvalue_int_content v x_16))

(* let[@axiom] llvm_int_1 = *)
(*  fun (v : dvalue) -> *)
(*   (dvalue_int_size v 1)#==>(dvalue_int_content v 1 || dvalue_int_content v 0) *)

(* let[@axiom] llvm_int_8 = *)
(*  fun (v : dvalue) -> *)
(*   (dvalue_int_size v 8) #==> (fun ((y [@ex]) : int) -> *)
(*   0 <= x_6 && x_6 <= 255 && dvalue_int_content v y) *)

(** Herdtool7 *)

let[@axiom] Herdtool7_literal =
 fun (v : literal) ->
  implies (wf_literal v)
    ((fun ((x_51 [@exists]) : int) -> herd_l_int v x_51)
    || herd_l_bool v true || herd_l_bool v false
    || (fun ((x_53 [@exists]) : char list) ->
      (fun (x_54 : char) ->
        implies (list_mem x_53 x_54) (x_54 == '0' || x_54 == '1'))
      && herd_l_bitvector v x_53)
    || (fun ((x_55 [@exists]) : float) -> herd_l_real v x_55)
    || fun ((x_56 [@exists]) : string) -> herd_l_string v x_56)

(** Old *)

(* let[@axiom] stlc_num_arr_geq_0 (tau : stlc_ty) (n : int) = *)
(*   (num_arr tau n)#==>(n >= 0) *)

(* let[@axiom] stlc_num_arr_arr (tau : stlc_ty) (tau_body : stlc_ty) (m : int) = *)
(*   (stlc_ty_arr2 tau tau_body)#==>(iff *)
(*                                     (num_arr tau_body (m - 1)) *)
(*                                     (num_arr tau m)) *)

(* let[@axiom] stlc_const_num_app_0 (v : stlc_term) (n : int) = *)
(*   (is_const v && num_app v n)#==>(n == 0) *)

(* let[@axiom] stlc_app_num_app_geq_0 (v : stlc_term) (n : int) = *)
(*   (is_app v && num_app v n)#==>(n > 0) *)

(* let[@axiom] stlc_var_num_app_0 (v : stlc_term) (n : int) = *)
(*   (is_var v && num_app v n)#==>(n == 0) *)

(* let[@axiom] stlc_num_app_gt_0_is_abs_or_app (v : stlc_term) (n : int) = *)
(*   (num_app v n && n > 0)#==>(is_abs v || is_app v) *)

(* let[@axiom] stlc_typing_num_arr (gamma : stlc_tyctx) (v : stlc_term) *)
(*     (tau : stlc_ty) ((n [@ex]) : int) = *)
(*   (typing gamma v tau)#==>(num_arr tau n) *)

(* let[@axiom] stlc_term_4_cases (v : stlc_term) = *)
(*   is_const v || is_var v || is_abs v || is_app v *)

(* let[@axiom] stlc_term_disjoint1 (v : stlc_term) = not (is_const v && is_var v) *)
(* let[@axiom] stlc_term_disjoint2 (v : stlc_term) = not (is_const v && is_abs v) *)
(* let[@axiom] stlc_term_disjoint3 (v : stlc_term) = not (is_const v && is_app v) *)
(* let[@axiom] stlc_term_disjoint4 (v : stlc_term) = not (is_var v && is_abs v) *)
(* let[@axiom] stlc_term_disjoint5 (v : stlc_term) = not (is_var v && is_app v) *)
(* let[@axiom] stlc_term_disjoint6 (v : stlc_term) = not (is_abs v && is_app v) *)

(* let[@axiom] stlc_term_const_typing_nat (gamma : stlc_tyctx) (v : stlc_term) *)
(*     (tau : stlc_ty) = *)
(*   (is_const v && typing gamma v tau)#==>(stlc_ty_nat tau) *)

(* let[@axiom] stlc_id_is_var (v : stlc_term) (id : int) = *)
(*   (stlc_id v id)#==>(is_var v) *)

(* let[@axiom] stlc_const_is_const (v : stlc_term) (c : int) = *)
(*   (stlc_const v c)#==>(is_const v) *)

(* let[@axiom] stlc_term_destruct1 (term : stlc_term) ((c [@ex]) : int) = *)
(*   (is_const term)#==>(stlc_const term c) *)

(* let[@axiom] stlc_term_destruct2 (term : stlc_term) ((c [@ex]) : int) = *)
(*   (is_var term)#==>(stlc_id term c) *)

(* let[@axiom] stlc_term_destruct3 (term : stlc_term) ((t1 [@ex]) : stlc_term) *)
(*     ((t2 [@ex]) : stlc_term) = *)
(*   (is_app term)#==>(stlc_app1 term t1 && stlc_app2 term t2) *)

(* let[@axiom] stlc_term_destruct4 (term : stlc_term) ((ty [@ex]) : stlc_ty) *)
(*     ((body [@ex]) : stlc_term) = *)
(*   (is_abs term)#==>(stlc_abs_ty term ty && stlc_abs_body term body) *)

(* let[@axiom] stlc_term_abs_typing_arr (gamma : stlc_tyctx) (v : stlc_term) *)
(*     (tau : stlc_ty) (ty : stlc_ty) (body : stlc_term) *)
(*     ((body_ty [@ex]) : stlc_ty) = *)
(*   (stlc_abs_ty v ty && stlc_abs_body v body && typing gamma v tau)#==>(stlc_ty_arr1 *)
(*                                                                          tau ty *)
(*                                                                      && stlc_ty_arr2 *)
(*                                                                           tau *)
(*                                                                           body_ty *)
(*                                                                       ) *)

(* let[@axiom] stlc_typing_app_tau_destruct (gamma : stlc_tyctx) (v : stlc_term) *)
(*     (tau : stlc_ty) (t1 : stlc_term) (t2 : stlc_term) = *)
(*   (typing gamma v tau && stlc_app1 v t1 && stlc_app2 v t2) *)
(*   #==> (fun ((func_ty [@ex]) : stlc_ty) ((arg_ty [@ex]) : stlc_ty) -> *)
(*   stlc_ty_arr1 func_ty arg_ty *)
(*   && stlc_ty_arr2 func_ty tau && typing gamma t1 func_ty *)
(*   && typing gamma t2 arg_ty) *)

(* let[@axiom] stlc_tyctx_cons (ty : stlc_ty) (gamma : stlc_tyctx) *)
(*     ((v [@ex]) : stlc_tyctx) = *)
(*   stlc_tyctx_hd v ty && stlc_tyctx_tl v gamma *)

(* let[@axiom] stlc_num_app_geq_0 (v : stlc_term) (n : int) = *)
(*   (num_app v n)#==>(0 <= n) *)

(* let[@axiom] stlc_num_app_abs_body_eq (v : stlc_term) (body : stlc_term) *)
(*     (n : int) = *)
(*   (stlc_abs_body v body && num_app v n)#==>(num_app body n) *)

(* let[@axiom] stlc_num_app_abs_body_eq_rev (v : stlc_term) (body : stlc_term) *)
(*     (n : int) = *)
(*   (stlc_abs_body v body && num_app body n)#==>(num_app v n) *)

(* let[@axiom] stlc_num_app_app_rev (v : stlc_term) (t1 : stlc_term) *)
(*     (t2 : stlc_term) (n : int) = *)
(*   (stlc_app1 v t1 && stlc_app2 v t2 && num_app v n) *)
(*   #==> (fun ((m1 [@ex]) : int) ((m2 [@ex]) : int) -> *)
(*   num_app t1 m1 && num_app t2 m2 && m1 + m2 == n - 1) *)

(* let[@axiom] stlc_abd_typing_rev (gamma : stlc_tyctx) (v : stlc_term) *)
(*     (tau : stlc_ty) (ty : stlc_ty) (body : stlc_term) (body_ty : stlc_ty) *)
(*     (gamma1 : stlc_tyctx) = *)
(*   (typing gamma v tau && stlc_abs_ty v ty && stlc_abs_body v body *)
(*  && stlc_tyctx_hd gamma1 ty && stlc_tyctx_tl gamma1 gamma)#==>(typing gamma1 *)
(*                                                                  body body_ty) *)

(* let[@axiom] stlc_const_typing_nat (gamma : stlc_tyctx) (v : stlc_term) *)
(*     (tau : stlc_ty) = *)
(*   (is_const v && typing gamma v tau)#==>(stlc_ty_nat tau) *)
