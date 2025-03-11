let test1 (u : unit) : int =
  let (x : int) = int_gen () in
  if x > 0 then x else Err

let[@assert] test1 ?l:(u = ((true : [%v: unit]) [@over])) =
  (0 < v : [%v: int]) [@under]

let test2 (x : int) : int = if x > 0 then x else Err

let[@assert] test2 ?l:(u = ((true : [%v: int]) [@under])) =
  (0 < v : [%v: int]) [@under]

let test3 (u : unit) : int * int =
  let (x : int) = int_gen () in
  (x, x)

(* let[@assert] test3 ?l:(u = (true : [%v: unit]) [@over]) = *)
(*   (((fst v) == (snd v)) : [%v: int * int]) [@under] *)

let[@assert] test3 ?l:(u = ((true : [%v: unit]) [@over])) =
  (true : [%v: int * int]) [@under]

let[@assume] foo1 ?l:(u = ((true : [%v: int]) [@under])) =
  (v == 0 : [%v: int]) [@under]

let[@assume] foo2 ?l:(u = ((true : [%v: int]) [@under])) =
  (v == 0 : [%v: int]) [@under]

let test4 (x : int) : bool =
  let (y1 : int) = foo1 x in
  let (y2 : int) = foo2 x in
  y1 == y2

let[@assert] test4 ?l:(u = ((true : [%v: int]) [@under])) =
  (v : [%v: bool]) [@under]
