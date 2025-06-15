(* Re-export all modules for external use *)
include Ast
include Types  
include Interpreter

let create_trust_env () = emptyenv

let eval_with_trust (expr: exp) : evT =
    eval expr (create_trust_env ())

(* Helper functions for creating trust signatures *)
let make_param (name: ide) (trust: trust_level) : trust_param =
    { param_name = name; param_trust = trust }

let make_signature (params: trust_param list) (return_trust: trust_level) : trust_signature =
    { params = params; return_trust = return_trust }