open Ast
open Types

(* Runtime errors *)
exception TrustViolation of string
exception SecurityError of string
exception ModuleError of string
exception PluginError of string
exception ParameterError of string

(* Empty environment *)
let emptyenv = function _ -> UnBound

(* Binding between a string x and a primitive value evT *)
let bind (s: evT env) (x: ide) (v: evT) = 
    function (i: ide) -> if (i = x) then v else (s i)

let rec bind_params (env: evT env) (params: trust_param list) (args: evT list) : evT env =
    match (params, args) with
    | ([], []) -> env
    | (p::ps, a::as_) -> 
        let promoted_arg = promoteTrust p.param_trust a in
        let new_env = bind env p.param_name promoted_arg in
        bind_params new_env ps as_
    | _ -> raise (ParameterError "Parameter count mismatch")

(* Trust validation function *)
let is_safe_content (content: string) : bool =
    not (String.contains content '$')

(* -----LANGUAGE PRIMITIVES----- *)

(* Checks if a number is zero *)
let is_zero(x) = 
    match x with
    | Int(v, t) -> Bool(v = 0, t)
    | _ -> raise (TrustViolation "Type mismatch in is_zero")

(* Integer - String - Bool equality *)
let eq_values(x, y) =   
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 = v2, result_trust)
    | (String(v1, t1), String(v2, t2)) ->
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 = v2, result_trust)
    | (Bool(v1, t1), Bool(v2, t2)) ->
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 = v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in equality - incompatible types")

(* Integer addition *)     
let int_plus(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Int(v1 + v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in addition")

(* Integer subtraction *)
let int_sub(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Int(v1 - v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in subtraction")

(* Integer product *)
let int_times(x, y) =
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Int(v1 * v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in multiplication")
    
(* Integer division *)
let int_div(x, y) =
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        if v2 = 0 then raise (SecurityError "Division by zero")
        else
            let result_trust = min_trust_level [t1; t2] in
            Int(v1 / v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in division")

(* Comparison operations *)
let less_than(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 < v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in comparison")

let greater_than(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 > v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in comparison")

(* Logical operations *)
let bool_and(x,y) = 
    match (x, y) with
    | (Bool(v1, t1), Bool(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 && v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in logical and")

let bool_or(x,y) = 
    match (x, y) with
    | (Bool(v1, t1), Bool(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 || v2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in logical or")

let bool_not(x) = 
    match x with
    | Bool(v, t) -> Bool(not v, t)
    | _ -> raise (TrustViolation "Type mismatch in logical not")

let str_contains(x, y) =
    match (x, y) with
    | (String(str, t1), String(substr, t2)) ->
        let result_trust = min_trust_level [t1; t2] in
        (* Simple string contains check *)
        let contains s sub =
            let len_s = String.length s and len_sub = String.length sub in
            if len_sub = 0 then true
            else if len_s < len_sub then false
            else
                let rec check i =
                    if i > len_s - len_sub then false
                    else if String.sub s i len_sub = sub then true
                    else check (i + 1)
                in check 0
        in
        Bool(contains str substr, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in string contains")

let str_length(x) =
    match x with
    | String(str, t) -> Int(String.length str, t)
    | _ -> raise (TrustViolation "Type mismatch in string length")

let str_concat(x, y) =
    match (x, y) with
    | (String(s1, t1), String(s2, t2)) ->
        let result_trust = min_trust_level [t1; t2] in
        String(s1 ^ s2, result_trust)
    | _ -> raise (TrustViolation "Type mismatch in string concatenation")

let handle_validation_result validation_result value = 
    match validation_result with
    | Bool(true, Untrust) ->
        promoteTrust Trust value
    | Bool(false, Untrust) ->
        raise (SecurityError "Custom validation failed")
    | _ ->
        raise (TrustViolation "Validation function should return untrusted value, since it's handling untrusted values")

let downgrade_untrusted_result (func_trust: trust_level) (result: evT) : evT =
    match func_trust with
    | Untrust -> 
        (* If function is untrusted, downgrade any trusted results to untrusted *)
        (match result with
         | Int(v, Trust) -> Int(v, Untrust)
         | Bool(v, Trust) -> Bool(v, Untrust) 
         | String(v, Trust) -> String(v, Untrust)
         | Closure(p, b, e, Trust) -> Closure(p, b, e, Untrust)
         | RecClosure(f, p, b, e, Trust) -> RecClosure(f, p, b, e, Untrust)
         (* TrustClosures cannot be downgraded *)
         | TrustClosure(_, _, _) -> 
             raise (SecurityError "Untrusted function cannot produce TrustClosure")
         | Module(n, bs, es, env, Trust) -> Module(n, bs, es, env, Untrust)
         | _ -> result)
    | Trust -> result (* Trusted functions can return trusted results *)

let rec match_pattern (pattern: pattern) (value: evT) (env: evT env) : evT env option =
    match pattern with
    | PVar(id) -> Some (bind env id value)
    | PConst(const_exp) -> 
        let const_val = eval const_exp env in
        (match (const_val, value) with
         | (Int(v1, _), Int(v2, _)) when v1 = v2 -> Some env
         | (Bool(v1, _), Bool(v2, _)) when v1 = v2 -> Some env
         | (String(v1, _), String(v2, _)) when v1 = v2 -> Some env
         | _ -> None)
    | PWildcard -> Some env

and eval_match_cases (value: evT) (cases: match_case list) (env: evT env) : evT =
    match cases with
    | [] -> raise (TrustViolation "No matching pattern found")
    | (pattern, expr) :: rest ->
        (match match_pattern pattern value env with
         | Some new_env -> eval expr new_env
         | None -> eval_match_cases value rest env)

and eval_module_content (content: module_content) (env: evT env) (entries: ide list) : (ide * evT) list * ide list =
    match content with
    | ModuleLet(id, trust_level, expr, next) ->
        let value = eval expr env in
        let promoted_value = promoteTrust trust_level value in
        let new_env = bind env id promoted_value in
        let (bindings, final_entries) = eval_module_content next new_env entries in
        ((id, promoted_value) :: bindings, final_entries)
    | ModuleFun(id, signature, body, next) ->
        let func_value = TrustClosure(signature, body, env) in
        let new_env = bind env id func_value in
        let (bindings, final_entries) = eval_module_content next new_env entries in
        ((id, func_value) :: bindings, final_entries)
    | ModuleEntry(id, next) ->
        let (bindings, final_entries) = eval_module_content next env (id :: entries) in
        (bindings, final_entries)
    | ModuleEnd -> ([], entries)

(* Interpreter *)
and eval (e:exp) (s:evT env) : evT = 
    match e with
    | EInt(n) -> Int(n, Untrust)
    | CstTrue -> Bool(true, Untrust)
    | CstFalse -> Bool(false, Untrust)
    | EString(str) -> String(str, Untrust)
    | Den(i) -> (s i)

    | Prod(e1,e2) -> int_times((eval e1 s), (eval e2 s))
    | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
    | Diff(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
    | Div(e1, e2) -> int_div((eval e1 s), (eval e2 s))

    | IsZero(e1) -> is_zero (eval e1 s)
    | Eq(e1, e2) -> eq_values((eval e1 s), (eval e2 s))
    | LessThan(e1, e2) -> less_than((eval e1 s),(eval e2 s))
    | GreaterThan(e1, e2) -> greater_than((eval e1 s),(eval e2 s))

    | And(e1, e2) -> bool_and((eval e1 s),(eval e2 s))
    | Or(e1, e2) -> bool_or((eval e1 s),(eval e2 s))
    | Not(e1) -> bool_not(eval e1 s)

    | IfThenElse(e1, e2, e3) -> 
        (match eval e1 s with
         | Bool(true, _) -> eval e2 s
         | Bool(false, _) -> eval e3 s
         | _ -> raise (TrustViolation "If condition must be boolean"))
    
    | Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
    | Fun(arg, ebody) -> Closure(arg, ebody ,s , Untrust)
    | TrustFun(signature, body) -> TrustClosure(signature, body, s)
    | Letrec(f, arg, fBody, leBody) ->
        let benv = bind s f (RecClosure(f, arg, fBody ,s , Untrust)) in
            eval leBody benv
    | Apply(e1, e2) -> 
        let f = eval e1 s in
        let v = eval e2 s in
        (match f with
         | Closure(arg, body, env, trust_level) -> 
             let new_env = bind env arg v in
             let result = eval body new_env in
             (match (trust_level, getTrustLevel v) with
              | (Trust, Untrust) -> raise (TrustViolation "Trusted function called with untrusted argument")
              | _ -> downgrade_untrusted_result trust_level result)
         | RecClosure(fname, arg, body, env, trust_level) -> 
             let renv = bind env fname f in
             let new_env = bind renv arg v in
             let result = eval body new_env in
             (match (trust_level, getTrustLevel v) with
              | (Trust, Untrust) -> raise (TrustViolation "Trusted recursive function called with untrusted argument")
              | _ -> downgrade_untrusted_result trust_level result)
         | TrustClosure(signature, body, env) ->
             let params = signature.params in
             if List.length params = 1 then
                (* Single parameter: apply directly *)
                let args = [v] in
                if not (validateParams params args) then
                    raise (TrustViolation "Parameter trust level mismatch")
                else
                    let new_env = bind_params env params args in
                    let result = eval body new_env in
                    promoteTrust signature.return_trust result
             else
                (* Multiple parameters: return a new closure for partial application *)
                let new_signature = {
                    params = List.tl params;
                    return_trust = signature.return_trust;
                } in
                let new_env = bind env (List.hd params).param_name v in
                TrustClosure(new_signature, body, new_env)
         | _ -> raise (TrustViolation "Not a function"))

    (* Trust-specific constructs *)
    | TrustLet(i, trust_level, e, ebody) ->
        let value = eval e s in
        (* Check if it's trying to promote an untrusted function *)
        (match (trust_level, value) with
        | (Trust, Closure(_, _, _, Untrust)) ->
            raise (SecurityError ("Cannot promote untrusted function '" ^ i ^ "' to trusted level"))
        | (Trust, RecClosure(_, _, _, _, Untrust)) ->
            raise (SecurityError ("Cannot promote untrusted recursive function '" ^ i ^ "' to trusted level"))
        | _ -> 
            let promoted_value = promoteTrust trust_level value in
            eval ebody (bind s i promoted_value))

    | Validate(e) ->
        let value = eval e s in
        if getTrustLevel value = Trust then value
        else
            (match value with
            | String(content, Untrust) ->
                if is_safe_content content then String(content, Trust)
                else raise (SecurityError "Validation failed: unsafe content")
            | Int(v, Untrust) ->
                if v >= 0 then Int(v, Trust)
                else raise (SecurityError "Validation failed: negative integer")
            | Bool(v, Untrust) -> Bool(v, Trust)
            | _ -> raise (TrustViolation "Cannot validate already trusted or non-validatable data"))
    
    | ValidateWith(val_func_expr, value_expr) -> (
        let value = eval value_expr s in
        
        if getTrustLevel value = Trust then value
        else
            let val_func = eval val_func_expr s in
            match val_func with
            | TrustClosure(signature, body, env) ->
                let arg_name = 
                    match signature.params with
                    | p::_ -> p.param_name
                    | [] -> "input" 
                in
                let new_env = bind env arg_name value in
                let validation_result = eval body new_env in
                handle_validation_result validation_result value
            | Closure(arg, body, env, Trust) ->
                let new_env = bind env arg value in
                let validation_result = eval body new_env in
                handle_validation_result validation_result value
            | _ ->
                raise (TrustViolation "Validation must be performed by a trusted function")
        )

    | Module(name, content, entry_exprs) ->
        let entry_names = List.map (function Den(id) -> id | _ -> raise (ModuleError "Entry must be identifier")) entry_exprs in
        let (bindings, entries) = eval_module_content content s entry_names in
        let module_trust = calculate_module_trust bindings in
        Printf.printf "Module '%s' trust level calculated as: %s\n" name 
                     (if module_trust = Trust then "TRUSTED" else "UNTRUSTED");
        Module(name, bindings, entries, s, module_trust)

    | ModuleAccess(module_expr, method_name) ->
        (match eval module_expr s with
         | Module(_, bindings, entries, _, module_trust) ->
             if List.mem method_name entries then
                 (try 
                     let accessed_value = List.assoc method_name bindings in
                     let accessed_trust = getTrustLevel accessed_value in
                     if module_trust = Trust && accessed_trust = Trust then
                         Printf.printf "Trusted module method '%s' accessed\n" method_name
                     else if module_trust = Untrust then
                         Printf.printf "Untrusted module method '%s' accessed\n" method_name;
                     accessed_value
                  with Not_found -> raise (ModuleError ("Method " ^ method_name ^ " not found in module")))
             else raise (SecurityError ("Method " ^ method_name ^ " is not an entry point"))
         | _ -> raise (ModuleError "Not a module"))

    | Include(plugin_expr) ->
        (* Store the plugin expression with current env *)
        Plugin(plugin_expr, s)

    (* Execute with trusted function protection *)
    | Execute(plugin_expr, func_expr, args_expr) ->
        (match eval plugin_expr s with
         | Plugin(plugin_body, plugin_env) ->
             (* Check if plugin body contains trusted functions *)
             if expressionMightContainTrustedFunctions plugin_body plugin_env then (
                 Printf.printf "SECURITY VIOLATION BLOCKED: Attempt to pass trusted function to untrusted plugin\n";
                 raise (SecurityError "Cannot pass trusted functions to untrusted plugins")
             ) else (
                 Printf.printf "No trusted functions detected in plugin parameters\n";
                 
                 (* Evaluate function and arguments in current environment *)
                 let func_value = eval func_expr s in
                 let args_value = eval args_expr s in
                 
                 (* Check the evaluated function is not trusted *)
                 if containsTrustedFunctions func_value then (
                     Printf.printf "RUNTIME SECURITY VIOLATION BLOCKED: Evaluated function is trusted\n";
                     raise (SecurityError "Runtime check: Cannot execute trusted functions in untrusted plugins")
                 ) else (
                     Printf.printf "Function is untrusted, safe to execute in Plugin\n";
                     
                     match func_value with
                     | Closure(arg, body, _, Untrust) ->
                         let result_env = bind s arg args_value in
                         eval body result_env
                     | _ -> raise (PluginError "Plugin function must be an untrusted closure")
                 )
             )
         | _ -> raise (PluginError "Not a plugin"))

    | Assert(id, expected_trust) ->
        let value = s id in
        let actual_trust = getTrustLevel value in
        if actual_trust = expected_trust then value
        else raise (SecurityError ("Trust assertion failed for " ^ id))

    | Match(e, cases) -> 
        let value = eval e s in
        eval_match_cases value cases s
        
    | StrContains(e1, e2) -> str_contains((eval e1 s), (eval e2 s))
    | StrLength(e1) -> str_length(eval e1 s)
    | StrConcat(e1, e2) -> str_concat((eval e1 s), (eval e2 s))