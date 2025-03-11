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
  Pp.printf "⊢ @{<purple>%s@}\n" (short_str 100 e);
  Pp.printf "⇨ @{<teal>%s@}\n\n" ty

let pprint_typing_check ctx (e, ty) () =
  ctx ();
  Pp.printf "⊢ @{<purple>%s@}\n" (short_str 100 e);
  Pp.printf "⇦ @{<teal>%s@}\n\n" ty

let pprint_typing_app fname ctx (args, r) () =
  Pp.printf "@{<bold>Application Type Check (%s):@}\n" fname;
  ctx ();
  Pp.printf "⊢ @{<purple>%s → ? @}\n"
    (List.split_by " → " (fun (x, ty) -> spf "%s:%s" x (layout_rty ty)) args);
  Pp.printf "⇦ @{<teal>%s@}\n\n" @@ layout_rty r

let pprint_subtyping ctx (r1, r2) () =
  ctx ();
  Printf.printf "⊢ @{<purple>%s@}\n" (layout_rty r1);
  Printf.printf "<:@{<teal>%s@}\n\n" (layout_rty r2)

let pprint_nonempty ctx r () =
  Pp.printf "@{<bold>None-mptyness Check:@}\n";
  ctx ();
  Printf.printf "⊢@{<purple>%s@} is not empty\n\n" (layout_rty r)
