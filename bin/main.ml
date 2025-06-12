open Minicaml

let () =
    print_endline "Trust-Aware MiniCaml Interpreter";
    
    (* Simple test of the interpreter *)
    let test_expr = Sum(EInt(5), EInt(3)) in
    let result = eval test_expr emptyenv in
    
    match result with
    | Int(n) -> Printf.printf "Test result: %d\n" n
    | _ -> print_endline "Unexpected result type"