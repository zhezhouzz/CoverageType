open Language
(** Refinement type context *)

open Zutils
open Typectx

type built_in_ctx = { builtin_ctx : Nt.nt rty ctx; axioms : Nt.nt prop list }
