open TrustLang

let test_basic_arithmetic () =
    let expr = Sum(EInt(2), EInt(3)) in
    let result = eval expr emptyenv in
    match result with
    | Int(5) -> true
    | _ -> false

let test_boolean_operations () =
    let expr = And(CstTrue, CstFalse) in
    let result = eval expr emptyenv in
    match result with
    | Bool(false) -> true
    | _ -> false

let test_function_application () =
    let f = Fun("x", Sum(Den("x"), EInt(1))) in
    let app = Apply(f, EInt(5)) in
    let result = eval app emptyenv in
    match result with
    | Int(6) -> true
    | _ -> false

let test_recursive_function () =
    let myRP = Letrec("fact", "n",              
                     IfThenElse(Eq(Den("n"),EInt(0)),                      
                               EInt(1),                      
                               Prod(Den("n"),                           
                                   Apply(Den("fact"),                                  
                                        Diff(Den("n"),EInt(1))))),                             
                     Apply(Den("fact"),EInt(3))) in
    let result = eval myRP emptyenv in
    match result with
    | Int(6) -> true  (* 3! = 6 *)
    | _ -> false

let run_tests () =
    let tests = [
        ("Basic Arithmetic", test_basic_arithmetic);
        ("Boolean Operations", test_boolean_operations);
        ("Function Application", test_function_application);
        ("Recursive Function (Factorial)", test_recursive_function);
    ] in
    
    List.iter (fun (name, test) ->
        if test () then
            Printf.printf "✓ %s passed\n" name
        else
            Printf.printf "✗ %s failed\n" name
    ) tests

let () = run_tests ()