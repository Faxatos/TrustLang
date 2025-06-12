(* Identifiers *)
type ide = string

(* Types *)
type tname = TInt | TBool | TString | TClosure | TRecClosure | TUnBound

(* Abstract Expressions = expressions in abstract syntax, 
   they compose the Abstract Syntax Tree *)
type exp = 
    | EInt of int
    | CstTrue 
    | CstFalse
    | EString of string
    | Den of ide
    (* Binary operators from integers to integers *)
    | Sum of exp * exp
    | Diff of exp * exp
    | Prod of exp * exp
    | Div of exp * exp
    (* Operators from integers to booleans *)
    | IsZero of exp
    | Eq of exp * exp
    | LessThan of exp * exp
    | GreaterThan of exp * exp
    (* Boolean operators *)
    | And of exp * exp
    | Or of exp * exp
    | Not of exp
    (* Flow control, functions *)
    | IfThenElse of exp * exp * exp
    | Let of ide * exp * exp
    | Letrec of ide * ide * exp * exp
    | Fun of ide * exp
    | Apply of exp * exp

(* Polymorphic environment *)
type 't env = ide -> 't

(* Evaluation types = expressible types *)
type evT = 
    | Int of int 
    | Bool of bool 
    | String of string 
    | Closure of ide * exp * evT env 
    | RecClosure of ide * ide * exp * evT env
    | UnBound