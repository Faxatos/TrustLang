open Ast

(* Calculate the minimum trust level from a list of trust levels *)
let min_trust_level (levels: trust_level list) : trust_level =
    if List.for_all (fun t -> t = Trust) levels then Trust else Untrust

(* Extract trust level from eval type *)
let rec getTrustLevel (x: evT) : trust_level =
    match x with
    | Int(_, t) | Bool(_, t) | String(_, t) -> t
    | Closure(_, _, _, t) | RecClosure(_, _, _, _, t) -> t
    | TrustClosure(signature, _, _) -> signature.return_trust
    | Module(_, bindings, _, _, module_trust) -> module_trust
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
    | Module(_, bindings, _, _, module_trust) -> TModule(module_trust)
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
    | (TModule(Untrust), Module(_, _, _, _, _)) -> true  (* Untrusted context accepts any module *)
    | (TPlugin, Plugin(_, _)) -> true
    | (TUnBound, UnBound) -> true
    | _ -> false

(* Promote trust level *)
let promoteTrust (level: trust_level) (value: evT) : evT =
    match (level, value) with
    | (Trust, Int(v, _)) -> Int(v, Trust)
    | (Trust, Bool(v, _)) -> Bool(v, Trust)
    | (Trust, String(v, _)) -> String(v, Trust)
    | (Trust, Closure(p, b, e, _)) -> Closure(p, b, e, Trust)
    | (Trust, RecClosure(f, p, b, e, _)) -> RecClosure(f, p, b, e, Trust)
    | _ -> value

(* Validate parameter trust levels *)
let validateParams (params: trust_param list) (args: evT list) : bool =
    if List.length params <> List.length args then false
    else
        List.for_all2 (fun param arg ->
            let arg_trust = getTrustLevel arg in
            match param.param_trust with
            | Trust -> arg_trust = Trust
            | Untrust -> true  (* Untrusted parameters accept any trust level *)
        ) params args

(* Check if a value contains trusted functions *)
let rec containsTrustedFunctions (value: evT) : bool =
    match value with
    | Closure(_, _, _, Trust) -> true
    | RecClosure(_, _, _, _, Trust) -> true
    | TrustClosure(signature, _, _) when signature.return_trust = Trust -> true
    | Module(_, bindings, _, _, _) ->
        List.exists (fun (_, v) -> containsTrustedFunctions v) bindings
    | _ -> false

(* Check --recursively-- if an expression might evaluate to trusted functions *)
let rec expressionMightContainTrustedFunctions (expr: exp) (env: evT env) : bool =
    match expr with
    | Den(id) -> 
        (match env id with
         | UnBound -> false
         | value -> containsTrustedFunctions value)
    | ModuleAccess(module_expr, _) ->
        (* Module access might return trusted functions *)
        true
    | Apply(_, _) -> 
        (* Function application might return trusted functions *)
        true
    | Let(_, _, body) | TrustLet(_, _, _, body) -> 
        expressionMightContainTrustedFunctions body env
    | IfThenElse(_, then_expr, else_expr) ->
        expressionMightContainTrustedFunctions then_expr env ||
        expressionMightContainTrustedFunctions else_expr env
    | TrustFun(sig, _) when sig.return_trust = Trust -> true
    | Fun(_, _) -> false  (* Regular functions are untrusted by default *)
    | _ -> false