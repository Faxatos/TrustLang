open Ast

exception SecurityError of string

(* Calculate the minimum trust level from a list of trust levels *)
let min_trust_level (levels: trust_level list) : trust_level =
    if List.for_all (fun t -> t = Trust) levels then Trust else Untrust

(* Extract trust level from eval type *)
let rec getTrustLevel (x: evT) : trust_level =
    match x with
    | Int(_, t) | Bool(_, t) | String(_, t) -> t
    | Closure(_, _, _, t) | RecClosure(_, _, _, _, t) -> t
    | TrustClosure(signature, _, _) -> signature.return_trust
    | Module(_, _, _, _, module_trust) -> module_trust
    | Plugin(_, _) -> Untrust
    | UnBound -> Untrust

(* Calculate module trust level based on its contents *)
and calculate_module_trust (bindings: (ide * evT) list) : trust_level =
    if bindings = [] then Trust
    else
        let trust_levels = List.map (fun (_, value) -> getTrustLevel value) bindings in
        min_trust_level trust_levels

(* Function from evT to tname that maps each value to its type descriptor *)
let getType (x: evT) : tname =
    match x with
    | Int(_, t) -> TInt(t)
    | Bool(_, t) -> TBool(t)
    | String(_, t) -> TString(t)
    | Closure(_, _, _, t) -> TClosure(t)
    | RecClosure(_, _, _, _, t) -> TRecClosure(t)
    | TrustClosure(signature, _, _) -> TClosure(signature.return_trust)
    | Module(_, _, _, _, module_trust) -> TModule(module_trust)
    | Plugin(_, _) -> TPlugin
    | UnBound -> TUnBound

(* Trust-aware type checking *)
let typecheck ((expected, actual) : (tname * evT)) : bool =
    match (expected, actual) with
    | (TInt(Trust), Int(_, Trust)) -> true
    | (TInt(Untrust), Int(_, _)) -> true
    | (TBool(Trust), Bool(_, Trust)) -> true
    | (TBool(Untrust), Bool(_, _)) -> true
    | (TString(Trust), String(_, Trust)) -> true
    | (TString(Untrust), String(_, _)) -> true
    | (TClosure(Trust), Closure(_, _, _, Trust)) -> true
    | (TClosure(Trust), TrustClosure(signature, _, _)) when signature.return_trust = Trust -> true
    | (TClosure(Untrust), Closure(_, _, _, _)) -> true
    | (TClosure(Untrust), TrustClosure(_, _, _)) -> true
    | (TRecClosure(Trust), RecClosure(_, _, _, _, Trust)) -> true
    | (TRecClosure(Untrust), RecClosure(_, _, _, _, _)) -> true
    | (TModule(Trust), Module(_, _, _, _, Trust)) -> true
    | (TModule(Untrust), Module(_, _, _, _, _)) -> true
    | (TPlugin, Plugin(_, _)) -> true
    | (TUnBound, UnBound) -> true
    | _ -> false

(* Promote trust level - only used by Validate and ValidateWith *)
let promoteTrust (value: evT) : evT =
    match value with
    | Int(v, _) -> Int(v, Trust)
    | Bool(v, _) -> Bool(v, Trust)
    | String(v, _) -> String(v, Trust)
    | _ -> raise (SecurityError "Only basic data types can be promoted to trusted")

(* Trust validation function *)
let is_safe_content (content: string) : bool =
    not (String.contains content '$')

(* Validate and promote untrusted data to trusted when declared with TrustLet *)
let validateTrustedBinding (value: evT) : evT =
    match value with
    (* Already trusted values - pass through *)
    | Int(_, Trust) | Bool(_, Trust) | String(_, Trust) -> value
    | Closure(_, _, _, Trust) | RecClosure(_, _, _, _, Trust) -> value
    | TrustClosure(_, _, _) -> value (* TrustClosures are inherently trusted *)
    | Module(_, _, _, _, Trust) -> value
    (* Untrusted data that can be validated and promoted *)
    | String(content, Untrust) ->
        if is_safe_content content then String(content, Trust)
        else raise (SecurityError "TrustLet validation failed: unsafe string content")
    | Int(v, Untrust) ->
        if v >= 0 then Int(v, Trust)
        else raise (SecurityError "TrustLet validation failed: negative integer")
    | Bool(v, Untrust) -> Bool(v, Trust)
    (* Untrusted functions cannot be bound with TrustLet *)
    | Closure(_, _, _, Untrust) -> 
        raise (SecurityError "TrustLet cannot bind untrusted functions - use Let for Fun, TrustLet for TrustFun")
    | RecClosure(_, _, _, _, Untrust) -> 
        raise (SecurityError "TrustLet cannot bind untrusted recursive functions - use Let for Fun, TrustLet for TrustFun")
    | Module(_, _, _, _, Untrust) -> 
        raise (SecurityError "TrustLet cannot bind untrusted modules")
    | Plugin(_, _) -> 
        raise (SecurityError "TrustLet cannot bind plugins")
    | UnBound -> 
        raise (SecurityError "TrustLet cannot bind unbound values")

(* Enforce untrusted binding - used by Let *)
let enforceUntrustedBinding (value: evT) : evT =
    match value with
    | Int(_, Trust) -> raise (SecurityError "Let can only bind untrusted values - trusted values require TrustLet")
    | Bool(_, Trust) -> raise (SecurityError "Let can only bind untrusted values - trusted values require TrustLet")
    | String(_, Trust) -> raise (SecurityError "Let can only bind untrusted values - trusted values require TrustLet")
    | Closure(_, _, _, Trust) -> raise (SecurityError "Let can only bind untrusted values - trusted functions require TrustLet")
    | RecClosure(_, _, _, _, Trust) -> raise (SecurityError "Let can only bind untrusted values - trusted functions require TrustLet")
    | TrustClosure(_, _, _) -> raise (SecurityError "Let can only bind untrusted values - TrustClosure requires TrustLet")
    | Module(_, _, _, _, Trust) -> raise (SecurityError "Let can only bind untrusted values - trusted modules require TrustLet")
    (* Accept all untrusted values *)
    | Int(_, Untrust) | Bool(_, Untrust) | String(_, Untrust) -> value
    | Closure(_, _, _, Untrust) | RecClosure(_, _, _, _, Untrust) -> value
    | Module(_, _, _, _, Untrust) -> value
    | Plugin(_, _) -> value (* Plugins are always untrusted *)
    | UnBound -> value

(* Validate parameter trust levels *)
let validateParams (params: trust_param list) (args: evT list) : bool =
    if List.length params <> List.length args then false
    else if params = [] then true  (* Handle empty parameter list *)
    else
        List.for_all2 (fun param arg ->
            let arg_trust = getTrustLevel arg in
            match param.param_trust with
            | Trust -> arg_trust = Trust
            | Untrust -> true
        ) params args

(* Check --recursively-- if an expression might evaluate to trusted functions *)
let rec expressionMightContainTrustedFunctions (expr: exp) (env: evT env) : bool =
    match expr with
    | Den(id) -> 
        (match env id with
         | UnBound -> false
         | value -> containsTrustedFunctions value)
    | ModuleAccess(_, _) -> true
    | Apply(e1, e2) ->
        expressionMightContainTrustedFunctions e1 env ||
        expressionMightContainTrustedFunctions e2 env
    | Let(_, e, body) | TrustLet(_, e, body) -> 
        expressionMightContainTrustedFunctions e env ||
        expressionMightContainTrustedFunctions body env
    | IfThenElse(cond, then_expr, else_expr) ->
        expressionMightContainTrustedFunctions cond env ||
        expressionMightContainTrustedFunctions then_expr env ||
        expressionMightContainTrustedFunctions else_expr env
    | TrustFun(signature, body) -> 
        if signature.return_trust = Trust then true
        else expressionMightContainTrustedFunctions body env
    | Fun(_, body) -> 
        expressionMightContainTrustedFunctions body env
    | _ -> false

(* Check if a value contains trusted functions *)
and containsTrustedFunctions (value: evT) : bool =
    match value with
    | Closure(_, _, _, Trust) -> true
    | RecClosure(_, _, _, _, Trust) -> true
    | TrustClosure(signature, body, env) ->
        signature.return_trust = Trust ||
        expressionMightContainTrustedFunctions body env
    | Module(_, bindings, _, _, _) ->
        List.exists (fun (_, v) -> containsTrustedFunctions v) bindings
    | Plugin(body, env) ->
        expressionMightContainTrustedFunctions body env
    | _ -> false