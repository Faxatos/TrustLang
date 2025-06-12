open Ast
open Types

(* Runtime errors *)
exception RuntimeError of string

(* Empty environment *)
let emptyenv = function _ -> UnBound

(* Binding between a string x and a primitive value evT *)
let bind (s: evT env) (x: ide) (v: evT) = 
    function (i: ide) -> if (i = x) then v else (s i)

(* -----LANGUAGE PRIMITIVES----- *)

(* Checks if a number is zero *)
let is_zero(x) = match (typecheck(TInt,x),x) with
    | (true, Int(v)) -> Bool(v = 0)
    | (_, _) -> raise (RuntimeError "Wrong type")

(* Integer equality *)
let int_eq(x,y) =   
    match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> Bool(v = w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

(* Integer addition *)     
let int_plus(x, y) = 
    match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> Int(v + w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

(* Integer subtraction *)
let int_sub(x, y) = 
    match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> Int(v - w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

(* Integer product *)
let int_times(x, y) =
    match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> Int(v * w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")
    
(* Integer division *)
let int_div(x, y) =
    match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> 
                    if w<>0 then Int(v / w)
                            else raise (RuntimeError "Division by zero")
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

(* Comparison operations *)
let less_than(x, y) = 
    match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> Bool(v < w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

let greater_than(x, y) = 
    match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
    | (true, true, Int(v), Int(w)) -> Bool(v > w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

(* Logical operations *)
let bool_and(x,y) = 
    match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
    | (true, true, Bool(v), Bool(w)) -> Bool(v && w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

let bool_or(x,y) = 
    match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
    | (true, true, Bool(v), Bool(w)) -> Bool(v || w)
    | (_,_,_,_) -> raise (RuntimeError "Wrong type")

let bool_not(x) = 
    match (typecheck(TBool,x), x) with
    | (true, Bool(v)) -> Bool(not(v))
    | (_,_) -> raise (RuntimeError "Wrong type")

(* Interpreter *)
let rec eval (e:exp) (s:evT env) : evT = 
    match e with
    | EInt(n) -> Int(n)
    | CstTrue -> Bool(true)
    | CstFalse -> Bool(false)
    | EString(s) -> String(s)
    | Den(i) -> (s i)

    | Prod(e1,e2) -> int_times((eval e1 s), (eval e2 s))
    | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
    | Diff(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
    | Div(e1, e2) -> int_div((eval e1 s), (eval e2 s))

    | IsZero(e1) -> is_zero (eval e1 s)
    | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
    | LessThan(e1, e2) -> less_than((eval e1 s),(eval e2 s))
    | GreaterThan(e1, e2) -> greater_than((eval e1 s),(eval e2 s))

    | And(e1, e2) -> bool_and((eval e1 s),(eval e2 s))
    | Or(e1, e2) -> bool_or((eval e1 s),(eval e2 s))
    | Not(e1) -> bool_not(eval e1 s)

    | IfThenElse(e1,e2,e3) -> 
        let g = eval e1 s in 
            (match (typecheck(TBool,g),g) with
            |(true, Bool(true)) -> eval e2 s
            |(true, Bool(false)) -> eval e3 s
            |(_,_) -> raise (RuntimeError "Wrong type")
            )
    | Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
    | Fun(arg, ebody) -> Closure(arg,ebody,s)
    | Letrec(f, arg, fBody, leBody) ->
        let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
            eval leBody benv
    | Apply(eF, eArg) ->
        let fclosure = eval eF s in 
            (match fclosure with 
            | Closure(arg, fbody, fDecEnv) -> 
                let aVal = eval eArg s in 
                let aenv = bind fDecEnv arg aVal in 
                eval fbody aenv 
            | RecClosure(f, arg, fbody, fDecEnv) -> 
                let aVal = eval eArg s in
                let rEnv = bind fDecEnv f fclosure in
                let aenv = bind rEnv arg aVal in 
                eval fbody aenv
            | _ -> raise ( RuntimeError "Wrong type")
            )