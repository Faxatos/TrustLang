open Ast

(* Function from evT to tname that maps each value to its type descriptor *)
let getType (x: evT) : tname =
    match x with
    | Int(_) -> TInt
    | Bool(_) -> TBool
    | String(_) -> TString
    | Closure(_,_,_) -> TClosure
    | RecClosure(_,_,_,_) -> TRecClosure
    | UnBound -> TUnBound

(* Type-checking *)
let typecheck ((x, y) : (tname * evT)) = 
    match x with
    | TInt -> (match y with 
               | Int(_) -> true
               | _ -> false
               )
    | TBool -> (match y with 
                | Bool(_) -> true
                | _ -> false
                )
    | TString -> (match y with
                 | String(_) -> true
                 | _ -> false
                 )
    | TClosure -> (match y with
                   | Closure(_,_,_) -> true
                   | _ -> false
                   )
    | TRecClosure -> (match y with
                     | RecClosure(_,_,_,_) -> true
                     | _ -> false
                     )
    | TUnBound -> (match y with
                 | UnBound -> true
                 | _ -> false
                 )