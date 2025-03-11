let[@axiom] ax1 =
 fun ((v [@forall]) : int tree) ->
  fun ((n [@forall]) : int) ->
   implies (n >= 0) (fun ((tr [@exists]) : int tree) ->
       treeNumNode tr == n && fun ((x [@exists]) : int) ->
       fun ((lt [@exists]) : int tree) ->
        fun ((rt [@exists]) : int tree) ->
         root tr x && lch tr lt && rch tr rt
         && fun ((x_0 [@exists]) : int) ->
         x_0 == treeNumNode lt && implies (treeNumNode v == x_0) (v == lt))

let[@axiom] ax2 =
 fun ((v [@forall]) : int tree) ->
  fun ((n [@forall]) : int) ->
   implies (n >= 0) (fun ((dummy_16 [@exists]) : int tree) ->
       fun ((tr [@exists]) : int tree) ->
        treeNumNode tr == n && fun ((x [@exists]) : int) ->
        fun ((lt [@exists]) : int tree) ->
         fun ((rt [@exists]) : int tree) ->
          root tr x && lch tr lt && rch tr rt
          && fun ((x_0 [@exists]) : int) ->
          x_0 == treeNumNode lt && fun ((l1 [@exists]) : int list) ->
          implies (treeNumNode dummy_16 == x_0) (dummy_16 == lt)
          && x_0 < n && x_0 >= 0
          && listLen l1 == x_0
          && fun ((x_2 [@exists]) : int) ->
          x_2 == treeNumNode rt && implies (treeNumNode v == x_2) (v == rt))

(* let[@axiom] tree_parent_of_lch_ex (v : int tree) (n : int) *)
(*     ((tr [@exists]) : int tree) ((r [@exists]) : int) *)
(*     ((rt [@exists]) : int tree) = *)
(*   treeNumNode tr == n && root tr r && lch tr v && rch tr rt *)

(* let[@axiom] tree_parent_of_rch_ex (v : int tree) (n : int) *)
(*     ((tr [@exists]) : int tree) ((r [@exists]) : int) *)
(*     ((lt [@exists]) : int tree) = *)
(*   treeNumNode tr == n && root tr r && lch tr lt && rch tr v *)

(* let[@axiom] treeNumNode_ex (v : int tree) ((n [@exists]) : int) = *)
(*   treeNumNode v == n *)
