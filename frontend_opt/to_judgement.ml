open Zutils
open Prop
open To_rty
open To_raw_term

let pprint_basic_typing ctx (e, ty) =
  Typectx.pprint_ctx Nt.layout ctx;
  Printf.printf "⊢\n";
  Printf.printf "%s :\n%s\n" (layout_term e) (Nt.layout ty)

let pprint_typing ctx (e, ty) =
  Typectx.pprint_ctx layout_rty ctx;
  Printf.printf "⊢\n";
  Printf.printf "%s :\n%s\n" (layout_term e) (layout_rty ty)

let playout_subtyping ctx (r1, r2) =
  Typectx.pprint_ctx layout_rty ctx;
  Printf.printf "⊢\n";
  Printf.printf "%s <:\n%s\n" (layout_rty r1) (layout_rty r2)
