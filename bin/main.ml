open Trustlang

(* Helper function to execute test with expected failure and capture exception message *)
let execWithFailure test =
  let value, success =
    try 
      let result = eval_with_trust test in
      Printf.printf " Test Passed unexpectedly with result: %s\n" 
        (match result with
         | Int(v, t) -> Printf.sprintf "Int(%d, %s)" v (if t = Trust then "Trust" else "Untrust")
         | Bool(v, t) -> Printf.sprintf "Bool(%b, %s)" v (if t = Trust then "Trust" else "Untrust")
         | String(v, t) -> Printf.sprintf "String(%s, %s)" v (if t = Trust then "Trust" else "Untrust")
         | _ -> "Other");
      (Bool(false, Untrust), false)
    with 
    | TrustViolation msg ->
        Printf.printf " Test Failed with TrustViolation: \027[31m%s\027[0m\n" msg;
        (Bool(false, Untrust), false)
    | SecurityError msg ->
        Printf.printf " Test Failed with SecurityError: \027[31m%s\027[0m\n" msg;
        (Bool(false, Untrust), false)
    | ModuleError msg ->
        Printf.printf " Test Failed with ModuleError: \027[31m%s\027[0m\n" msg;
        (Bool(false, Untrust), false)
    | PluginError msg ->
        Printf.printf " Test Failed with PluginError: \027[31m%s\027[0m\n" msg;
        (Bool(false, Untrust), false)
    | ParameterError msg ->
        Printf.printf " Test Failed with ParameterError: \027[31m%s\027[0m\n" msg;
        (Bool(false, Untrust), false)
    | exn ->
        Printf.printf " Test Failed with unexpected exception: \027[31m%s\027[0m\n" (Printexc.to_string exn);
        (Bool(false, Untrust), false)
  in
  assert (match value with Bool(false, _) -> true | _ -> false);
  assert (not success)

(* Helper function to execute successful test *)
let execWithSuccess test =
  try 
    let result = eval_with_trust test in
    Printf.printf " Test Passed with result: %s\n" 
      (match result with
       | Int(v, t) -> Printf.sprintf "Int(%d, %s)" v (if t = Trust then "Trust" else "Untrust")
       | Bool(v, t) -> Printf.sprintf "Bool(%b, %s)" v (if t = Trust then "Trust" else "Untrust")
       | String(v, t) -> Printf.sprintf "String(%s, %s)" v (if t = Trust then "Trust" else "Untrust")
       | Module(name, _, _, _, t) -> Printf.sprintf "Module(%s, %s)" name (if t = Trust then "Trust" else "Untrust")
       | _ -> "Other");
    result
  with exn ->
    Printf.printf " Test Failed unexpectedly with exception: \027[31m%s\027[0m\n" (Printexc.to_string exn);
    failwith "Test should have succeeded"

let print_separator() =
  print_string "-------------------------------------------------------------------------------------\n"

let print_example_header test_name =
  print_separator();
  Printf.printf " %s\n" test_name

let run_examples () =
  Printf.printf "\n TrustLang examples (inspired from assignment text) \n\n";

  print_example_header "Example 1: Basic variable declarations with trust levels";
  let _ = execWithSuccess(
    TrustLet("val", EString("aba"),
             Let("val1", EString("cdc"),
                 Den("val")))
  ) in

  print_example_header "Example 2: Trusted functions with validation and string operations";
  let _ = execWithSuccess(
    (* Declare p_trusted: concatenates "hello" with input string *)
    TrustLet("p_trusted",
        TrustFun(make_signature [make_param "data" Trust] Trust,
                TrustLet("myh", EString("hello"),
                        StrConcat(Den "myh", Den "data"))),
    
    (* Declare is_safe: validates untrusted strings *)
    TrustLet("is_safe",
        TrustFun(make_signature [make_param "text" Untrust] Trust,
                Not(StrContains(Den "text", EString("malicious")))),
    
    (* Declare validate: promotes valid strings to trusted *)
    TrustLet("validate",
        TrustFun(make_signature [make_param "input" Untrust] Trust,
                TrustLet("safe_check", Apply(Den "is_safe", Den "input"),
                    IfThenElse(Den "safe_check",
                              ValidateWith(Den "is_safe", Den "input"),
                              TrustLet("failed", EString("validation_failed"), Den "failed")))),
    
    (* Test the functions - using TrustLet for trusted operations *)
    TrustLet("safe_data", EString("_world"),
        TrustLet("result1", Apply(Den "p_trusted", Den "safe_data"),
            Let("untrusted_input", EString("user_input"),
                Apply(Den "validate", Den "untrusted_input")))))))
  ) in

  print_example_header "Example 3: Authentication module with secure password checking";
  let _ = execWithSuccess(
    TrustLet("authentication",
        Module("AuthModule",
               (* Store the trusted password *)
               ModuleTrustLet("password", EString("abcd"),
                        (* is_safe function for validation *)
                        ModuleTrustLet("is_safe",
                                 TrustFun(make_signature [make_param "text" Untrust] Trust,
                                         Not(StrContains(Den("text"), EString("malicious")))),
                                 (* validate function *)
                                 ModuleTrustLet("validate",
                                          TrustFun(make_signature [make_param "input" Untrust] Trust,
                                                  TrustLet("safe_check",
                                                      Apply(Den("is_safe"), Den("input")),
                                                      IfThenElse(Den("safe_check"),
                                                                ValidateWith(Den("is_safe"), Den("input")),
                                                                EString("validation_failed")))),
                                          (* checkPsw function *)
                                          ModuleTrustLet("checkPsw",
                                                   TrustFun(make_signature [make_param "g" Untrust] Trust,
                                                           TrustLet("handle",
                                                               Apply(Den("validate"), Den("g")),
                                                               (* Check if validated input equals password *)
                                                               Eq(Den("handle"), Den("password")))),
                                                   ModuleEntry("checkPsw", ModuleEnd))))),
               [Den("checkPsw")]),
        (* Test the authentication *)
        Let("test_input", EString("abcd"),
            Apply(ModuleAccess(Den("authentication"), "checkPsw"), Den("test_input"))))
  ) in

  print_example_header "Example 4: Plugin security vulnerability - Trusted function leakage prevention";
  
  (* Legitimate use case: create a simple filter-like plugin that processes numbers *)
  let _ = execWithSuccess(
    Let("myFilter", 
        Include(EInt(42)),
        (* Create an untrusted even number checker *)
        Let("even_checker", Fun("n", Eq(Sum(Den("n"), EInt(0)), Prod(Div(Den("n"), EInt(2)), EInt(2)))),
            (* Execute plugin with the checker - this should work *)
            Execute(Den("myFilter"), Den("even_checker"), EInt(4))))
  ) in

  (* Now demonstrate the security violation attempt *)
  Printf.printf "\n--- Security Attack Prevention ---\n";
  let _ = execWithFailure(
    (* Recreate the authentication module *)
    TrustLet("my_trust_module",
        Module("AttackTarget",
               ModuleTrustLet("password", EString("secret_password"),
                        ModuleTrustLet("checkPsw",
                                 TrustFun(make_signature [make_param "input" Untrust] Trust,
                                         Eq(Den("input"), Den("password"))),
                                 ModuleEntry("checkPsw", ModuleEnd))),
               [Den("checkPsw")]),
        (* Attempt the attack: try to extract trusted function for use in plugin *)
        TrustLet("myAttack", ModuleAccess(Den("my_trust_module"), "checkPsw"),
            Let("myFilter", Include(EInt(1)),
                (* Trying to pass trusted function to plugin (should fail) *)
                Execute(Den("myFilter"), Den("myAttack"), EString("test_password")))))
  ) in

  print_example_header "Example 5: Proper plugin usage with untrusted functions";
  let _ = execWithSuccess(
    (* Create an untrusted module that can be safely used in plugins *)
    Let("untrusted_utils",
        Module("UntrustedUtils",
               ModuleLet("simple_check",
                        Fun("x", GreaterThan(StrLength(Den("x")), EInt(3))),
                        ModuleEntry("simple_check", ModuleEnd)),
               [Den("simple_check")]),
        (* This is safe: untrusted function can be used in plugins *)
        Let("myFilter", Include(EInt(1)),
            Execute(Den("myFilter"), 
                   ModuleAccess(Den("untrusted_utils"), "simple_check"), 
                   EString("hello"))))
  ) in

  print_separator();
  Printf.printf "\n TrustLang examples completed\n"

(* Main entry point *)
let () = run_examples ()