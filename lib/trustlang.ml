(* Re-export all modules *)
module Ast = Ast
module Types = Types
module Interpreter = Interpreter

include Ast
include Types
include Interpreter

(* Test that constructors are available *)
let test_constructors () =
    let _ = EInt(42) in  (* This should compile if Ast is properly included *)
    let _ = Trust in     (* This should compile if Types is properly included *)
    ()

let create_trust_env () = emptyenv

let eval_with_trust (expr: exp) : evT =
    eval expr (create_trust_env ())

(* Helper functions for creating trust signatures *)
let make_param (name: ide) (trust: trust_level) : trust_param =
    { param_name = name; param_trust = trust }

let make_signature (params: trust_param list) (return_trust: trust_level) : trust_signature =
    { params = params; return_trust = return_trust }