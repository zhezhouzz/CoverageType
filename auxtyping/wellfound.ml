open Language
open Zutils

let make_order_constraint a x =
  let a = (AVar a) #: a.ty in
  let x = (AVar x) #: x.ty in
  let lt = "<" #: Nt.(construct_arr_tp ([ Ty_int; Ty_int ], Ty_bool)) in
  let geq = ">=" #: Nt.(construct_arr_tp ([ Ty_int; Ty_int ], Ty_bool)) in
  let ty = Nt._type_unify [%here] a.ty x.ty in
  match ty with
  | Nt.Ty_int ->
      And
        [
          Lit (AAppOp (lt, [ x; a ])) #: Nt.Ty_bool;
          Lit (AAppOp (geq, [ x; (AC (I 0)) #: Nt.Ty_int ])) #: Nt.Ty_bool;
        ]
  | _ -> _failatwith [%here] "unimp"
