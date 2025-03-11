val bind : (unit -> 'a) -> ('a -> unit -> 'b) -> unit -> 'b

(* let union (g1 : unit -> int) (g2 : unit -> int) : unit -> int = *)
(*   let (x : bool) = bool_gen () in *)
(*   if x then g1 else g2 *)

(* let[@assert] union *)
(*     ?l:(u1 = *)
(*         fun ?l:(tmp1 = ((true : [%v: unit]) [@over])) -> *)
(*           ((v == 1 : [%v: int]) [@under])) *)
(*     ?l:(u2 = *)
(*         fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) -> *)
(*           ((v == 2 : [%v: int]) [@under])) = *)
(*  fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) -> *)
(*   ((v == 2 : [%v: int]) [@under]) *)

let union (g1 : unit -> int) (g2 : unit -> int) : unit -> int =
  bind bool_gen (fun (x : bool) -> if x then g1 else g2)

let[@assert] union
    ?l:(u1 =
        fun ?l:(tmp1 = ((true : [%v: unit]) [@over])) ->
          ((v == 1 : [%v: int]) [@under]))
    ?l:(u2 =
        fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) ->
          ((v == 2 : [%v: int]) [@under])) =
 fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) ->
  ((v == 2 : [%v: int]) [@under])
