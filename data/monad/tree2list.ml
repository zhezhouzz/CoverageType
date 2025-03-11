let[@library] tree_num_node ?l:(tr = ((true : [%v: int tree]) [@over])) =
  (v == treeNumNode tr : [%v: int]) [@under]

let[@library] list_concat ?l:(l1 = ((true : [%v: int list]) [@over]))
    ?l:(l2 = ((true : [%v: int list]) [@over])) =
  (listLen v == listLen l1 + listLen l2 : [%v: int list]) [@under]

let rec flatten (n : int) (tr : int tree) : int list =
  match tr with
  | Leaf -> []
  | Node (x, lt, rt) ->
      let (l1 : int list) = flatten (tree_num_node lt) lt in
      let (l2 : int list) = flatten (tree_num_node rt) rt in
      x :: list_concat l1 l2

let[@assert] flatten ?l:(n = ((v >= 0 : [%v: int]) [@over]))
    ?l:(tr = ((treeNumNode v == n : [%v: int tree]) [@under])) =
  (listLen v == n : [%v: int list]) [@under]

(* let[@library] flatten ?l:(n = ((v >= 0 : [%v: int]) [@over])) *)
(*     ?l:(tr = ((treeNumNode v == n : [%v: int tree]) [@under])) = *)
(*   (listLen v == n : [%v: int list]) [@under] *)

let list_gen (tree_gen : unit -> int tree) : unit -> int list =
  fmap
    (fun (tr : int tree) ->
      let (res : int list) = flatten (tree_num_node tr) tr in
      res)
    tree_gen

let[@assert] list_gen
    ?l:(u1 =
        fun ?l:(tmp1 = ((true : [%v: unit]) [@over])) ->
          ((true : [%v: int tree]) [@under])) =
 fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) ->
  ((true : [%v: int list]) [@under])
