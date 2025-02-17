open Language
open Zutils

let make_order_constraint a x =
  let a = (AVar a) #: a.ty in
  let x = (AVar x) #: x.ty in
  let lt = "<" #: Nt.(construct_arr_tp ([ int_ty; int_ty ], bool_ty)) in
  let geq = ">=" #: Nt.(construct_arr_tp ([ int_ty; int_ty ], bool_ty)) in
  let ty = Nt._type_unify [%here] a.ty x.ty in
  if Nt.equal_nt Nt.int_ty ty then
    And
      [
        Lit (AAppOp (lt, [ x; a ])) #: Nt.bool_ty;
        Lit (AAppOp (geq, [ x; (AC (I 0)) #: Nt.int_ty ])) #: Nt.bool_ty;
      ]
  else _failatwith [%here] "unimp"
