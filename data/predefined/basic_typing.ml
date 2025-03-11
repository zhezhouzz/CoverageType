(** The datatype constructor should use the lower case instead of the first char
*)
type unit = TT

type bool = True | False
type 'a list = Nil | Cons of 'a * 'a list
type 'a pairinghp = Phpleaf | Phpnode of 'a * 'a pairinghp list
type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree
type 'a heap = Hempty | Hnode of 'a * 'a heap * 'a heap
type 'a set = Sempty | Snode of 'a * 'a set * 'a set
type 'a binomialhp = Bhpleaf | Bhpnode of int * 'a * 'a binomialhp list
type 'a rbtree = Rbtleaf | Rbtnode of bool * 'a rbtree * 'a * 'a rbtree
type 'a skewhp = Shpnode of int * 'a * 'a list * 'a skewhp list
type 'a splayhp = Sphpleaf | Sphpnode of 'a splayhp * 'a * 'a splayhp
type 'a unbset = Usleaf | Usnode of 'a * 'a unbset * 'a unbset
type 'a batchedq = Batchedq of 'a list * 'a list
type 'a lazyty = Lazyty of 'a
type 'a stream = Streamnil | Streamlazycons of 'a * 'a stream lazyty
type 'a bankersq = Bankersq of int * 'a stream * int * 'a stream
type 'a ulist = Unil | Ucons of 'a * 'a ulist
type 'a ctree = Cleaf | Cnode of 'a * 'a ctree * 'a ctree

type 'a leftisthp =
  | Lhpleaf
  | Lhpnode of int * 'a * 'a leftisthp * 'a leftisthp

type stlc_ty = Stlc_ty_nat | Stlc_ty_arr of stlc_ty * stlc_ty

type stlc_term =
  | Stlc_const of int
  | Stlc_id of int
  | Stlc_app of stlc_term * stlc_term
  | Stlc_abs of stlc_ty * stlc_term

type stlc_tyctx = Stlc_tyctx_nil | Stlc_tyctx_cons of stlc_ty * stlc_tyctx

(** Monad *)

val bind : (unit -> 'a) -> ('a -> unit -> 'b) -> unit -> 'b
val fmap : ('a -> 'b) -> (unit -> 'a) -> unit -> 'b

(** Arithmatic operators *)

val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int

(** Builtin generators *)

val int_range : int -> int -> int
val bool_gen : unit -> bool
val int_gen : unit -> int
val nat_gen : unit -> int
val int_range_inc : int -> int -> int
val int_range_inex : int -> int -> int
val increment : int -> int
val decrement : int -> int
val lt_eq_one : int -> bool
val gt_eq_int_gen : int -> int
val sizecheck : int -> bool
val subs : int -> int
val dummy : unit

(** Method predicates (needs to be stratificated) *)

(** pair *)

(* val fst : 'a * 'b -> 'a *)
(* val snd : 'a * 'b -> 'b *)

(** lists *)

val len : 'a list -> int -> bool
val emp : 'a list -> bool
val hd : 'a list -> 'a -> bool
val tl : 'a list -> 'a list -> bool
val list_mem : 'a list -> 'a -> bool
val sorted : 'a list -> bool
val uniq : 'a list -> bool
val listLen : 'a list -> int

(* for tree *)
val depth : 'a tree -> int -> bool
val leaf : 'a tree -> bool
val root : 'a tree -> 'a -> bool
val lch : 'a tree -> 'a tree -> bool
val rch : 'a tree -> 'a tree -> bool
val tree_mem : 'a tree -> 'a -> bool
val bst : 'a tree -> bool
val heap : 'a tree -> bool
val complete : 'a tree -> bool
val treeNumNode : 'a tree -> int

(* for rbtree *)
val num_black : 'a rbtree -> int -> bool
val rb_leaf : 'a rbtree -> bool
val rb_root : 'a rbtree -> 'a -> bool
val rb_root_color : 'a rbtree -> bool -> bool
val rb_lch : 'a rbtree -> 'a rbtree -> bool
val rb_rch : 'a rbtree -> 'a rbtree -> bool
val no_red_red : 'a rbtree -> bool

(* for stream *)
val forc : 'a stream lazyty -> 'a stream
val _forc : int -> int
val stream_len : 'a stream -> int -> bool
val stream_emp : 'a stream -> bool
val stream_hd : 'a stream -> 'a -> bool
val stream_tl : 'a stream -> 'a stream -> bool

(* for bankersq *)
val bankersq_len : 'a bankersq -> int -> bool
val bankersq1 : 'a bankersq -> int -> bool
val bankersq2 : 'a bankersq -> 'a stream -> bool
val bankersq3 : 'a bankersq -> int -> bool
val bankersq4 : 'a bankersq -> 'a stream -> bool

(* for batchedq *)
val batchedq_len : 'a batchedq -> int -> bool
val batchedq1 : 'a batchedq -> 'a list -> bool
val batchedq2 : 'a batchedq -> 'a list -> bool

(* for leftisthp *)
val leftisthp_depth : 'a leftisthp -> int -> bool
val leftisthp_leaf : 'a leftisthp -> bool
val leftisthp_root : 'a leftisthp -> 'a -> bool
val leftisthp_rank : 'a leftisthp -> int -> bool
val leftisthp_lch : 'a leftisthp -> 'a leftisthp -> bool
val leftisthp_rch : 'a leftisthp -> 'a leftisthp -> bool

(* for stlc *)
val is_const : stlc_term -> bool
val is_var : stlc_term -> bool
val is_abs : stlc_term -> bool
val is_app : stlc_term -> bool
val typing : stlc_tyctx -> stlc_term -> stlc_ty -> bool
val num_app : stlc_term -> int -> bool

(* val dec_pair : stlc_ty -> int -> int -> bool *)
val num_arr : stlc_ty -> int -> bool
val stlc_ty_nat : stlc_ty -> bool
val stlc_ty_arr1 : stlc_ty -> stlc_ty -> bool
val stlc_ty_arr2 : stlc_ty -> stlc_ty -> bool
val stlc_const : stlc_term -> int -> bool
val stlc_id : stlc_term -> int -> bool
val stlc_app1 : stlc_term -> stlc_term -> bool
val stlc_app2 : stlc_term -> stlc_term -> bool
val stlc_abs_ty : stlc_term -> stlc_ty -> bool
val stlc_abs_body : stlc_term -> stlc_term -> bool
val stlc_tyctx_emp : stlc_tyctx -> bool
val stlc_tyctx_hd : stlc_tyctx -> stlc_ty -> bool
val stlc_tyctx_tl : stlc_tyctx -> stlc_tyctx -> bool
