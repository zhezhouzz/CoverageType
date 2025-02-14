open Zutils
open Prop
open To_rty
open To_raw_term
open Zdatatype

let pprint_basic_typing ctx (e, ty) () =
  ctx ();
  Printf.printf "⊢\n";
  Printf.printf "%s :\n%s\n" (layout_raw_term e) (Nt.layout ty)

let pprint_typing_infer ctx (e, ty) () =
  ctx ();
  Pp.printf "⊢ @{<hi_magenta>%s@} ⇨\n" (short_str 100 e);
  Pp.printf "  @{<cyan>%s@}\n\n" ty

let pprint_typing_check ctx (e, ty) () =
  ctx ();
  Pp.printf "⊢ @{<hi_magenta>%s@} ⇦\n" (short_str 100 e);
  Pp.printf "  @{<cyan>%s@}\n\n" ty

let pprint_typing_app fname ctx (args, r) () =
  Pp.printf "@{<bold>Application Type Check (%s):@}\n" fname;
  ctx ();
  Pp.printf "⊢ @{<hi_magenta>%s → ? @} ⇦\n"
    (List.split_by " → " (fun (x, ty) -> spf "%s:%s" x (layout_rty ty)) args);
  Pp.printf "  @{<cyan>%s@}\n\n" @@ layout_rty r

let pprint_subtyping ctx (r1, r2) () =
  ctx ();
  Printf.printf "⊢ @{<hi_magenta>%s@} <:\n" (layout_rty r1);
  Printf.printf "  @{<cyan>%s@}\n\n" (layout_rty r2)

let pprint_nonempty ctx r () =
  Pp.printf "@{<bold>None-mptyness Check:@}\n";
  ctx ();
  Printf.printf "⊢@{<hi_magenta>%s@} is not empty\n\n" (layout_rty r)
