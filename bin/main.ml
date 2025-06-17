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

let print_test_header test_name =
  print_separator();
  Printf.printf " %s\n" test_name

let run_examples  () =
  Printf.printf "\n=== TRUSTLANG EXAMPLES ===\n\n";

  (* Example 1: Basic variable declarations with trust levels *)
  print_example_header "Example 1: Basic variable declarations with trust levels";
  let _ = execWithSuccess(
    TrustLet("val", Trust, EString("aba"),
             Let("val1", EString("cdc"),
                 Den("val")))
  ) in

  (* Example 2: Trusted functions with validation logic *)
  print_example_header "Example 2: Trusted functions with validation and string operations";
  let _ = execWithSuccess(
    (* Define a trusted concatenation-like function using string contains for demo *)
    Let("trusted_module",
        Module("StringOps",
               (* p_trusted function: simulates string concatenation by checking if data contains "hello" *)
               ModuleLet("p_trusted", Trust,
                        TrustFun(make_signature [make_param "data" Trust] Trust,
                                Let("myh", EString("hello"),
                                    IfThenElse(StrContains(Den("data"), Den("myh")),
                                              EString("hello_combined"),
                                              EString("hello_default")))),
                        (* is_safe function: validates that string doesn't contain "malicious" *)
                        ModuleLet("is_safe", Trust,
                                 TrustFun(make_signature [make_param "text" Untrust] Trust,
                                         Not(StrContains(Den("text"), EString("malicious")))),
                                 (* validate function: validates input and returns it if safe *)
                                 ModuleLet("validate", Trust,
                                          TrustFun(make_signature [make_param "input" Untrust] Trust,
                                                  Let("safe_check", 
                                                      Apply(ModuleAccess(Den("trusted_module"), "is_safe"), Den("input")),
                                                      IfThenElse(Den("safe_check"),
                                                                ValidateWith(Fun("x", CstTrue), Den("input")),
                                                                EString("validation_failed")))),
                                          ModuleEntry("p_trusted",
                                                     ModuleEntry("is_safe", 
                                                                ModuleEntry("validate", ModuleEnd)))))),
               [Den("p_trusted"); Den("is_safe"); Den("validate")]),
        (* Test the functions *)
        TrustLet("safe_data", Trust, EString("hello_world"),
                Let("unsafe_data", EString("malicious_code"),
                    Apply(ModuleAccess(Den("trusted_module"), "p_trusted"), Den("safe_data")))))
  ) in

  (* Example 3: Authentication module with password checking *)
  (* Original: Authentication module with password validation *)
  print_example_header "Example 3: Authentication module with secure password checking";
  let _ = execWithSuccess(
    Let("authentication",
        Module("AuthModule",
               (* Store the trusted password *)
               ModuleLet("password", Trust, EString("abcd"),
                        (* is_safe function for validation *)
                        ModuleLet("is_safe", Trust,
                                 TrustFun(make_signature [make_param "text" Untrust] Trust,
                                         Not(StrContains(Den("text"), EString("malicious")))),
                                 (* validate function *)
                                 ModuleLet("validate", Trust,
                                          TrustFun(make_signature [make_param "input" Untrust] Trust,
                                                  Let("safe_check",
                                                      Apply(ModuleAccess(Den("authentication"), "is_safe"), Den("input")),
                                                      IfThenElse(Den("safe_check"),
                                                                ValidateWith(Fun("x", CstTrue), Den("input")),
                                                                EString("validation_failed")))),
                                          (* checkPsw function *)
                                          ModuleLet("checkPsw", Trust,
                                                   TrustFun(make_signature [make_param "g" Untrust] Trust,
                                                           Let("handle",
                                                               Apply(ModuleAccess(Den("authentication"), "validate"), Den("g")),
                                                               (* Check if validated input equals password *)
                                                               Eq(Den("handle"), ModuleAccess(Den("authentication"), "password")))),
                                                   ModuleEntry("checkPsw", ModuleEnd))))),
               [Den("checkPsw")]),
        (* Test the authentication *)
        Let("test_input", EString("abcd"),
            Apply(ModuleAccess(Den("authentication"), "checkPsw"), Den("test_input"))))
  ) in

  (* Example 4: Plugin security vulnerability demonstration *)
  (* Original: Filter function with security attack simulation *)
  print_example_header "Example 4: Plugin security vulnerability - Trusted function leakage prevention";
  
  (* First show a legitimate use case *)
  let _ = execWithSuccess(
    (* Create a simple filter-like plugin that processes numbers *)
    Let("myFilter", 
        Include(EInt(42)), (* Simple plugin code *)
        (* Create an even number checker (simulating the even function) *)
        Let("even_checker", Fun("n", Eq(Sum(Den("n"), EInt(0)), Prod(Div(Den("n"), EInt(2)), EInt(2)))),
            (* Execute plugin with the checker - this should work *)
            Execute(Den("myFilter"), Den("even_checker"), EInt(4))))
  ) in

  (* Now demonstrate the security violation attempt *)
  Printf.printf "\n--- Security Attack Prevention ---\n";
  execWithFailure(
    (* Recreate the authentication module *)
    Let("my_trust_module",
        Module("AttackTarget",
               ModuleLet("password", Trust, EString("secret_password"),
                        ModuleLet("checkPsw", Trust,
                                 TrustFun(make_signature [make_param "input" Untrust] Trust,
                                         Eq(Den("input"), ModuleAccess(Den("my_trust_module"), "password"))),
                                 ModuleEntry("checkPsw", ModuleEnd))),
               [Den("checkPsw")]),
        (* Attempt the attack: try to extract trusted function for use in plugin *)
        Let("myAttack", ModuleAccess(Den("my_trust_module"), "checkPsw"),
            Let("myFilter", Include(EInt(1)),
                (* This should fail - trying to pass trusted function to plugin *)
                Execute(Den("myFilter"), Den("myAttack"), EString("test_password")))))
  );

  (* Example 5: Demonstrate proper plugin usage with untrusted functions *)
  print_example_header "Example 5: Proper plugin usage with untrusted functions";
  let _ = execWithSuccess(
    (* Create an untrusted module that can be safely used in plugins *)
    Let("untrusted_utils",
        Module("UntrustedUtils",
               ModuleLet("simple_check", Untrust,
                        Fun("x", GreaterThan(StrLength(Den("x")), EInt(3))),
                        ModuleEntry("simple_check", ModuleEnd)),
               [Den("simple_check")]),
        (* This is safe - untrusted function can be used in plugins *)
        Let("myFilter", Include(EInt(1)),
            Execute(Den("myFilter"), 
                   ModuleAccess(Den("untrusted_utils"), "simple_check"), 
                   EString("hello"))))
  ) in

  print_separator();
  Printf.printf "\n=== HOMEWORK EXAMPLES COMPLETED ===\n";

(* Main entry point *)
let () = run_examples ()