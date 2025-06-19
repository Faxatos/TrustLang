open Ast
open Types

(* Empty environment *)
let emptyenv = function _ -> UnBound

(* Binding between a string x and a primitive value evT *)
let bind (s: evT env) (x: ide) (v: evT) = 
    function (i: ide) -> if (i = x) then v else (s i)

let rec bind_params (env: evT env) (params: trust_param list) (args: evT list) : evT env =
    match (params, args) with
    | ([], []) -> env
    | (p::ps, a::as_) -> 
        (* For TrustFun parameters, validate trust levels *)
        let validated_arg = 
            match p.param_trust with
            | Trust -> 
                if getTrustLevel a = Trust then a
                else raise (TrustViolation ("Parameter " ^ p.param_name ^ " requires trusted argument"))
            | Untrust -> a
        in
        let new_env = bind env p.param_name validated_arg in
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
    | _ -> raise (ParameterError "Type mismatch in is_zero")

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
    | _ -> raise (ParameterError "Type mismatch in equality - incompatible types")

(* Integer addition *)     
let int_plus(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Int(v1 + v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in addition")

(* Integer subtraction *)
let int_sub(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Int(v1 - v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in subtraction")

(* Integer product *)
let int_times(x, y) =
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Int(v1 * v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in multiplication")
    
(* Integer division *)
let int_div(x, y) =
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        if v2 = 0 then raise (ParameterError "Division by zero")
        else
            let result_trust = min_trust_level [t1; t2] in
            Int(v1 / v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in division")

(* Comparison operations *)
let less_than(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 < v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in comparison")

let greater_than(x, y) = 
    match (x, y) with
    | (Int(v1, t1), Int(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 > v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in comparison")

(* Logical operations *)
let bool_and(x,y) = 
    match (x, y) with
    | (Bool(v1, t1), Bool(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 && v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in logical and")

let bool_or(x,y) = 
    match (x, y) with
    | (Bool(v1, t1), Bool(v2, t2)) -> 
        let result_trust = min_trust_level [t1; t2] in
        Bool(v1 || v2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in logical or")

let bool_not(x) = 
    match x with
    | Bool(v, t) -> Bool(not v, t)
    | _ -> raise (ParameterError "Type mismatch in logical not")

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
    | _ -> raise (ParameterError "Type mismatch in string contains")

let str_length(x) =
    match x with
    | String(str, t) -> Int(String.length str, t)
    | _ -> raise (ParameterError "Type mismatch in string length")

let str_concat(x, y) =
    match (x, y) with
    | (String(s1, t1), String(s2, t2)) ->
        let result_trust = min_trust_level [t1; t2] in
        String(s1 ^ s2, result_trust)
    | _ -> raise (ParameterError "Type mismatch in string concatenation")

let handle_validation_result validation_result value = 
    match validation_result with
    | Bool(true, _) -> promoteTrust value
    | Bool(false, _) -> raise (SecurityError "Custom validation failed")
    | _ -> raise (ParameterError "Validation function must return a boolean")

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

(* Deep copy function for evT values to prevent reference sharing *)
let rec deep_copy_value (value: evT) (original_env: evT env) : evT =
    match value with
    (* Basic data types - create new instances *)
    | Int(v, t) -> Int(v, t)
    | Bool(v, t) -> Bool(v, t)  
    | String(v, t) -> String(v, t)
    
    (* Function types - create new closures with copied environments *)
    | Closure(param, body, env, trust) ->
        let copied_env = copy_closure_environment env body original_env in
        Closure(param, body, copied_env, trust)
        
    | RecClosure(fname, param, body, env, trust) ->
        let copied_env = copy_closure_environment env body original_env in
        RecClosure(fname, param, body, copied_env, trust)
        
    | TrustClosure(signature, body, env) ->
        let copied_env = copy_closure_environment env body original_env in
        TrustClosure(signature, body, copied_env)
        
    (* Module types - create new module with copied bindings *)
    | Module(name, bindings, entries, env, trust) ->
        let copied_bindings = List.map (fun (id, value) -> (id, deep_copy_value value original_env)) bindings in
        let copied_env = copy_module_environment env original_env in
        Module(name, copied_bindings, entries, copied_env, trust)
        
    (* Plugin types - create new plugin with copied environment *)  
    | Plugin(expr, env) ->
        let copied_env = copy_plugin_environment env expr original_env in
        Plugin(expr, copied_env)
        
    | UnBound -> UnBound

(* Copy environment for closures - only copy variables that might be accessed *)
and copy_closure_environment (env: evT env) (body: exp) (fallback_env: evT env) : evT env =
    let free_vars = get_free_variables body in
    create_copied_env env free_vars fallback_env

(* Copy environment for modules *)
and copy_module_environment (env: evT env) (fallback_env: evT env) : evT env =
    fun id -> 
        let value = env id in
        if value = UnBound then fallback_env id
        else deep_copy_value value fallback_env

(* Copy environment for plugins *)  
and copy_plugin_environment (env: evT env) (expr: exp) (fallback_env: evT env) : evT env =
    let free_vars = get_free_variables expr in
    create_copied_env env free_vars fallback_env

(* Create a new environment with copied values for specified variables *)
and create_copied_env (source_env: evT env) (var_list: string list) (fallback_env: evT env) : evT env =
    fun id ->
        if List.mem id var_list then
            let value = source_env id in
            if value = UnBound then fallback_env id
            else deep_copy_value value fallback_env
        else fallback_env id

(* Get free variables in an expression for selective environment copying *)
and get_free_variables (expr: exp) : string list =
    let rec collect_vars bound_vars acc = function
        | EInt(_) | CstTrue | CstFalse | EString(_) -> acc
        | Den(id) -> if List.mem id bound_vars then acc else id :: acc
        
        | Sum(e1, e2) | Diff(e1, e2) | Prod(e1, e2) | Div(e1, e2)
        | Eq(e1, e2) | LessThan(e1, e2) | GreaterThan(e1, e2)
        | And(e1, e2) | Or(e1, e2) | StrContains(e1, e2) | StrConcat(e1, e2) ->
            let acc1 = collect_vars bound_vars acc e1 in
            collect_vars bound_vars acc1 e2
            
        | IsZero(e) | Not(e) | StrLength(e) | Validate(e) ->
            collect_vars bound_vars acc e
            
        | IfThenElse(cond, then_e, else_e) ->
            let acc1 = collect_vars bound_vars acc cond in
            let acc2 = collect_vars bound_vars acc1 then_e in
            collect_vars bound_vars acc2 else_e
            
        | Let(id, e, body) | TrustLet(id, e, body) ->
            let acc1 = collect_vars bound_vars acc e in
            collect_vars (id :: bound_vars) acc1 body
            
        | Letrec(fname, param, fbody, body) ->
            let new_bound = fname :: param :: bound_vars in
            let acc1 = collect_vars new_bound acc fbody in
            collect_vars (fname :: bound_vars) acc1 body
            
        | Fun(param, body) ->
            collect_vars (param :: bound_vars) acc body
            
        | TrustFun(signature, body) ->
            let param_names = List.map (fun p -> p.param_name) signature.params in
            collect_vars (param_names @ bound_vars) acc body
            
        | Apply(func, arg) ->
            let acc1 = collect_vars bound_vars acc func in
            collect_vars bound_vars acc1 arg
            
        | ValidateWith(func, value) ->
            let acc1 = collect_vars bound_vars acc func in
            collect_vars bound_vars acc1 value
            
        | ModuleAccess(module_expr, _) ->
            collect_vars bound_vars acc module_expr
            
        | Include(plugin_expr) ->
            collect_vars bound_vars acc plugin_expr
            
        | Execute(plugin_expr, func_expr, args_expr) ->
            let acc1 = collect_vars bound_vars acc plugin_expr in
            let acc2 = collect_vars bound_vars acc1 func_expr in
            collect_vars bound_vars acc2 args_expr
            
        | Assert(id, _) ->
            if List.mem id bound_vars then acc else id :: acc
            
        | Match(expr, cases) ->
            let acc1 = collect_vars bound_vars acc expr in
            List.fold_left (fun acc_case (pattern, case_expr) ->
                let pattern_vars = get_pattern_variables pattern in
                collect_vars (pattern_vars @ bound_vars) acc_case case_expr
            ) acc1 cases
            
        | Module(_, content, entries) ->
            let acc1 = collect_module_vars bound_vars acc content in
            List.fold_left (collect_vars bound_vars) acc1 entries
            
    and collect_module_vars bound_vars acc = function
        | ModuleLet(id, expr, next) | ModuleTrustLet(id, expr, next) ->
            let acc1 = collect_vars bound_vars acc expr in
            collect_module_vars (id :: bound_vars) acc1 next
        | ModuleEntry(_, next) ->
            collect_module_vars bound_vars acc next
        | ModuleEnd -> acc
            
    and get_pattern_variables = function
        | PVar(id) -> [id]
        | PConst(_) | PWildcard -> []
    in
    
    let vars = collect_vars [] [] expr in
    List.sort_uniq String.compare vars

(* Helper function to get a unique identifier for values (for debugging) *)
let get_value_identifier = function
    | Int(v, t) -> Printf.sprintf "Int(%d,%s)@%d" v (if t = Trust then "Trust" else "Untrust") (Hashtbl.hash v)
    | Bool(v, t) -> Printf.sprintf "Bool(%b,%s)@%d" v (if t = Trust then "Trust" else "Untrust") (Hashtbl.hash v)
    | String(v, t) -> Printf.sprintf "String(%s,%s)@%d" (String.sub v 0 (min 10 (String.length v))) (if t = Trust then "Trust" else "Untrust") (Hashtbl.hash v)
    | Closure(_, _, _, t) -> Printf.sprintf "Closure(%s)@%d" (if t = Trust then "Trust" else "Untrust") (Random.int 10000)
    | RecClosure(_, _, _, _, t) -> Printf.sprintf "RecClosure(%s)@%d" (if t = Trust then "Trust" else "Untrust") (Random.int 10000)
    | TrustClosure(_, _, _) -> Printf.sprintf "TrustClosure@%d" (Random.int 10000)
    | Module(name, _, _, _, t) -> Printf.sprintf "Module(%s,%s)@%d" name (if t = Trust then "Trust" else "Untrust") (Random.int 10000)
    | Plugin(_, _) -> Printf.sprintf "Plugin@%d" (Random.int 10000)
    | UnBound -> "UnBound"

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
    | ModuleLet(id, expr, next) ->
        let value = eval expr env in
        let untrusted_value = enforceUntrustedBinding value in 
        let new_env = bind env id untrusted_value in
        let (bindings, final_entries) = eval_module_content next new_env entries in
        ((id, untrusted_value) :: bindings, final_entries)
    | ModuleTrustLet(id, expr, next) ->
        let value = eval expr env in
        let trusted_value = validateTrustedBinding value in   
        let new_env = bind env id trusted_value in
        let (bindings, final_entries) = eval_module_content next new_env entries in
        ((id, trusted_value) :: bindings, final_entries)
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
         | _ -> raise (ParameterError "If condition must be boolean"))
    
    | Let(i, e, ebody) ->
        let value = eval e s in
        let untrusted_value = enforceUntrustedBinding value in
        eval ebody (bind s i untrusted_value)
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
                    if signature.return_trust = Trust then
                        (match result with
                         | Int(v, _) -> Int(v, Trust)
                         | Bool(v, _) -> Bool(v, Trust)
                         | String(v, _) -> String(v, Trust)
                         | _ -> result)
                    else result
             else
                (* Multiple parameters: return a new closure for partial application *)
                let new_signature = {
                    params = List.tl params;
                    return_trust = signature.return_trust;
                } in
                let new_env = bind env (List.hd params).param_name v in
                TrustClosure(new_signature, body, new_env)
         | _ -> raise (TrustViolation "Not a function"))

    | TrustLet(i, e, ebody) ->
        let value = eval e s in
        let validated_value = validateTrustedBinding value in
        eval ebody (bind s i validated_value)

    | Validate(e) ->
        let value = eval e s in
        (match value with
         | String(_, Trust) | Int(_, Trust) | Bool(_, Trust) -> value
         | String(content, Untrust) ->
             if is_safe_content content then promoteTrust value
             else raise (SecurityError "Validation failed: unsafe content")
         | Int(v, Untrust) ->
             if v >= 0 then promoteTrust value
             else raise (SecurityError "Validation failed: negative integer")
         | Bool(_, Untrust) -> promoteTrust value
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
     | Module(module_name, bindings, entries, _, module_trust) ->
         if List.mem method_name entries then
             (try 
                 let accessed_value = List.assoc method_name bindings in
                 let accessed_trust = getTrustLevel accessed_value in
                 
                 (* Create a deep copy of the accessed value *)
                 let copied_value = deep_copy_value accessed_value s in
                 
                 if module_trust = Trust && accessed_trust = Trust then
                     Printf.printf "Trusted module method '%s' accessed (COPIED)\n" method_name
                 else if module_trust = Untrust then
                     Printf.printf "Untrusted module method '%s' accessed (COPIED)\n" method_name;
                     
                 Printf.printf "Original value address: %s, Copied value address: %s\n"
                     (get_value_identifier accessed_value)
                     (get_value_identifier copied_value);
                     
                 copied_value
              with Not_found -> 
                 raise (ModuleError ("Method " ^ method_name ^ " not found in module " ^ module_name)))
         else 
             raise (SecurityError ("Method " ^ method_name ^ " is not an entry point in module " ^ module_name))
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
                 Printf.printf "Violation Blocked: Attempt to pass trusted function to untrusted plugin\n";
                 raise (SecurityError "Cannot pass trusted functions to untrusted plugins")
             ) else (
                 
                 let func_value = eval func_expr s in
                 let args_value = eval args_expr s in
                 
                 (* Check the evaluated function is not trusted *)
                 if containsTrustedFunctions func_value then (
                     Printf.printf "Violation Blocked: Evaluated function is trusted\n";
                     raise (SecurityError "Cannot execute trusted functions in untrusted plugins")
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