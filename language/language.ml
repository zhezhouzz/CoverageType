include Ast
include Prop
include Frontend_opt
open Zutils
open Zdatatype

let layout_rtyed_var { x; ty } = spf "%s:%s" x (layout_rty ty)
let layout_rtyed_vars l = List.split_by_comma layout_rtyed_var l
