(* See also logging in Zutils which has other tags *)
let tagged tag (f : unit -> unit) =
  if List.exists (String.equal tag) (TypecheckerConfig.get_log_tags ()) then
    f ()

let auxtyping = tagged "auxtyping"
let inline = tagged "inline"
let instantiate_rty = tagged "instantiateRty"
let instantiation = tagged "instantiation"
let normalization = tagged "normalization"
let preprocess = tagged "preprocess"
let result = tagged "result"
let typing = tagged "typing"
