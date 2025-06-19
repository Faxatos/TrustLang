(* Identifiers *)
type ide = string

(* Trust levels *)
type trust_level = Trust | Untrust

(* Extended types with trust annotations *)
type tname = 
    | TInt of trust_level
    | TBool of trust_level 
    | TString of trust_level
    | TClosure of trust_level
    | TRecClosure of trust_level
    | TModule of trust_level
    | TPlugin
    | TUnBound

(* Parameter with trust annotation *)
type trust_param = {
    param_name : ide;
    param_trust : trust_level;
}

(* Function signature with trust annotations *)
type trust_signature = {
    params : trust_param list;
    return_trust : trust_level;
}

(* Abstract Expressions = expressions in abstract syntax, 
   they compose the Abstract Syntax Tree *)
type exp = 
    | EInt of int
    | CstTrue 
    | CstFalse
    | EString of string
    | Den of ide
    (* Arithmetic operations *)
    | Sum of exp * exp
    | Diff of exp * exp
    | Prod of exp * exp
    | Div of exp * exp
    (* Comparison operations *)
    | IsZero of exp
    | Eq of exp * exp
    | LessThan of exp * exp
    | GreaterThan of exp * exp
    (* Boolean operations *)
    | And of exp * exp
    | Or of exp * exp
    | Not of exp
    (* Flow control, functions *)
    | IfThenElse of exp * exp * exp
    | Let of ide * exp * exp
    | Letrec of ide * ide * exp * exp
    | Fun of ide * exp
    | Apply of exp * exp
    (* Pattern matching *)
    | Match of exp * match_case list
    (* String operations *)
    | StrContains of exp * exp
    | StrLength of exp
    | StrConcat of exp * exp
    (* Trust primitives *)
    | TrustLet of ide  * exp * exp
    | TrustFun of trust_signature * exp
    | Validate of exp
    | ValidateWith of exp * exp
    | Module of ide * module_content * exp list
    | ModuleAccess of exp * ide
    | Include of exp
    | Execute of exp * exp * exp
    | Assert of ide * trust_level

(* Pattern matching types *)
and pattern = 
    | PVar of ide
    | PConst of exp
    | PWildcard

and match_case = pattern * exp

(* Module content structure *)
and module_content = 
    | ModuleLet of ide * exp * module_content          (* Always untrusted *)
    | ModuleTrustLet of ide * exp * module_content     (* Always trusted *)
    | ModuleEntry of ide * module_content
    | ModuleEnd

(* Polymorphic Environment *)
type 't env = ide -> 't

(* Extended evaluation types with trust information *)
type evT = 
    | Int of int * trust_level
    | Bool of bool * trust_level
    | String of string * trust_level
    | Closure of ide * exp * evT env * trust_level
    | RecClosure of ide * ide * exp * evT env * trust_level
    | TrustClosure of trust_signature * exp * evT env
    | Module of ide * (ide * evT) list * ide list * evT env * trust_level
    | Plugin of exp * evT env
    | UnBound