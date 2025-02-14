open Zutils
open Prop
open Sexplib.Std

type 't value =
  | VConst of constant
  | VVar of (('t, string) typed[@free])
  | VLam of {
      lamarg : (('t, string) typed[@bound]);
      body : ('t, 't term) typed;
    }
  | VFix of {
      fixname : (('t, string) typed[@bound]);
      fixarg : (('t, string) typed[@bound]);
      body : ('t, 't term) typed;
    }
  | VTuple of ('t, 't value) typed list

and 't term =
  | CErr
  | CVal of ('t, 't value) typed
  | CLetE of {
      rhs : ('t, 't term) typed;
      lhs : (('t, string) typed[@bound]);
      body : ('t, 't term) typed;
    }
  | CLetDeTuple of {
      turhs : ('t, 't value) typed;
      tulhs : (('t, string) typed list[@bound]);
      body : ('t, 't term) typed;
    }
  | CApp of { appf : ('t, 't value) typed; apparg : ('t, 't value) typed }
  | CAppOp of { op : ('t, op) typed; appopargs : ('t, 't value) typed list }
  | CMatch of {
      matched : ('t, 't value) typed;
      match_cases : 't match_case list;
    }

and 't match_case =
  | CMatchcase of {
      constructor : ('t, string) typed;
      args : (('t, string) typed list[@bound]);
      exp : ('t, 't term) typed;
    }
[@@deriving eq, ord, show, sexp]

type 't raw_term =
  | Var of (('t, string) typed[@free])
  | Const of constant
  | Lam of {
      lamarg : (('t, string) typed[@bound]);
      lambody : ('t, 't raw_term) typed;
    }
  | Err
  | Let of {
      if_rec : bool;
      rhs : ('t, 't raw_term) typed;
      lhs : (('t, string) typed list[@bound]);
      letbody : ('t, 't raw_term) typed;
    }
  | App of ('t, 't raw_term) typed * ('t, 't raw_term) typed list
  | AppOp of ('t, op) typed * ('t, 't raw_term) typed list
  | Ifte of
      ('t, 't raw_term) typed
      * ('t, 't raw_term) typed
      * ('t, 't raw_term) typed
  | Tuple of ('t, 't raw_term) typed list
  | Match of {
      matched : ('t, 't raw_term) typed;
      match_cases : 't raw_match_case list;
    }

and 't raw_match_case =
  | Matchcase of {
      constructor : ('t, string) typed;
      args : (('t, string) typed list[@bound]);
      exp : ('t, 't raw_term) typed;
    }
[@@deriving eq, ord, show, sexp]

type constructor_declaration = { constr_name : string; argsty : Nt.nt list }
[@@deriving eq, ord, show, sexp]

(* NOTE: vv is default variable *)
let default_v = "vv"

type 't cty = { nty : Nt.nt; phi : 't prop } [@@deriving eq, ord, show, sexp]
type ou = Over | Under [@@deriving eq, ord, show, sexp]
type arr_type = NormalArr | GhostOverBaseArr [@@deriving eq, ord, show, sexp]

type 't rty =
  | RtyBase of { ou : ou; cty : 't cty }
  | RtyArr of {
      arr_type : arr_type;
      argrty : 't rty;
      arg : (string[@bound]);
      retty : 't rty;
    }
  | RtyProd of 't rty * 't rty
[@@deriving eq, ord, show, sexp]

type 't item =
  | MTyDecl of {
      type_name : string;
      type_params : string list;
      type_decls : constructor_declaration list;
    }
  | MValDecl of ('t, string) typed
  | MMethodPred of ('t, string) typed
  | MAxiom of { name : string; prop : 't prop }
  | MFuncImpRaw of {
      name : ('t, string) typed;
      if_rec : bool;
      body : ('t, 't raw_term) typed;
    }
  | MFuncImp of {
      name : ('t, string) typed;
      if_rec : bool;
      body : ('t, 't term) typed;
    }
  | MRty of { is_assumption : bool; name : string; rty : 't rty }
[@@deriving eq, ord, show, sexp]
