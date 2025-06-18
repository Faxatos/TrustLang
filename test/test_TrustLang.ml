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

(* Main security tests *)
let run_security_suite () =
  Printf.printf "\n=== TRUSTLANG SECURITY TEST SUITE ===\n\n";

  (* Test 0: Basic trusted module creation and access *)
  print_test_header "Test_0: Basic trusted module with trusted functions";
  let _ = execWithSuccess(
    Module("TrustedMath", 
           ModuleLet("add", Trust, 
                    TrustFun(make_signature [make_param "x" Trust; make_param "y" Trust] Trust,
                            Sum(Den("x"), Den("y"))),
                    ModuleEntry("add", ModuleEnd)),
           [Den("add")])
  ) in

  (* Test 1: Access trusted module function normally with proper arguments *)
  print_test_header "Test_1: Access trusted module function with two trusted arguments";
  let _ = execWithSuccess(
    Let("trusted_module",
        Module("TrustedMath",
               ModuleLet("multiply", Trust,
                        TrustFun(make_signature [make_param "x" Trust; make_param "y" Trust] Trust,
                                Prod(Den("x"), Den("y"))),
                        ModuleEntry("multiply", ModuleEnd)),
               [Den("multiply")]),
        TrustLet("trusted_val1", Trust, EInt(5),
                TrustLet("trusted_val2", Trust, EInt(3),
                        Apply(Apply(ModuleAccess(Den("trusted_module"), "multiply"),
                                   Den("trusted_val1")),
                              Den("trusted_val2")))))
  ) in

  (* Test 2: Try to access non-entry point method (should fail) *)
  print_test_header "Test_2: Try to access non-entry point method";
  execWithFailure(
    Let("trusted_module",
        Module("TrustedMath",
               ModuleLet("secret_func", Trust,
                        TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
                        ModuleLet("public_func", Trust,
                                 TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
                                 ModuleEntry("public_func", ModuleEnd))),
               [Den("public_func")]),
        ModuleAccess(Den("trusted_module"), "secret_func"))
  );

  (* Test 3: Plugin execution with safe untrusted code *)
  print_test_header "Test_3: Plugin execution with safe untrusted code";
  let _ = execWithSuccess(
    Let("plugin",
        Include(Sum(EInt(5), EInt(10))),
        Let("safe_func", Fun("x", Sum(Den("x"), EInt(1))),
            Execute(Den("plugin"), Den("safe_func"), EInt(42))))
  ) in

  (* Test 4: Try to pass trusted function to plugin (should fail) *)
  print_test_header "Test_4: Try to pass trusted function to plugin";
  execWithFailure(
    Let("trusted_module",
        Module("TrustedMath",
               ModuleLet("trusted_add", Trust,
                        TrustFun(make_signature [make_param "x" Trust; make_param "y" Trust] Trust,
                                Sum(Den("x"), Den("y"))),
                        ModuleEntry("trusted_add", ModuleEnd)),
               [Den("trusted_add")]),
        Let("plugin", Include(EInt(42)),
            Execute(Den("plugin"), 
                   ModuleAccess(Den("trusted_module"), "trusted_add"), 
                   EInt(5))))
  );

  (* Test 5: Try to use trusted module function inside plugin definition (should fail) *)
  print_test_header "Test_5: Try to use trusted module function inside plugin";
  execWithFailure(
    Let("trusted_module",
        Module("TrustedMath",
               ModuleLet("trusted_multiply", Trust,
                        TrustFun(make_signature [make_param "x" Trust; make_param "y" Trust] Trust,
                                Prod(Den("x"), Den("y"))),
                        ModuleEntry("trusted_multiply", ModuleEnd)),
               [Den("trusted_multiply")]),
        Let("malicious_plugin",
            Include(Apply(ModuleAccess(Den("trusted_module"), "trusted_multiply"), EInt(5))),
            Execute(Den("malicious_plugin"), Fun("x", Den("x")), EInt(1))))
  );

  (* Test 6: Validation of untrusted data *)
  print_test_header "Test_6: Validation of untrusted data";
  let _ = execWithSuccess(
    Let("untrusted_str", EString("hello"),
        Validate(Den("untrusted_str")))
  ) in

  (* Test 7: Validation failure with unsafe content *)
  print_test_header "Test_7: Validation failure with unsafe content";
  execWithFailure(
    Let("unsafe_str", EString("hello$world"),
        Validate(Den("unsafe_str")))
  );

  (* Test 8: Trust assertion success *)
  print_test_header "Test_8: Trust assertion success";
  let _ = execWithSuccess(
    TrustLet("trusted_val", Trust, EInt(42),
             Assert("trusted_val", Trust))
  ) in

  (* Test 9: Trust assertion failure *)
  print_test_header "Test_9: Trust assertion failure";
  execWithFailure(
    Let("untrusted_val", EInt(42),
        Assert("untrusted_val", Trust))
  );

  (* Test 10: Pattern matching with trusted values *)
  print_test_header "Test_10: Pattern matching with trusted values";
  let _ = execWithSuccess(
    TrustLet("trusted_num", Trust, EInt(5),
             Match(Den("trusted_num"), 
                   [(PConst(EInt(5)), EString("matched"));
                    (PWildcard, EString("no match"))]))
  ) in

  (* Test 11: Complex module with mixed trust levels *)
  print_test_header "Test_11: Complex module with mixed trust levels";
  let _ = execWithSuccess(
    Module("MixedModule",
           ModuleLet("untrusted_val", Untrust, EInt(10),
                    ModuleLet("trusted_func", Trust,
                             TrustFun(make_signature [make_param "x" Untrust] Trust,
                                     Sum(Den("x"), EInt(1))),
                             ModuleEntry("untrusted_val",
                                        ModuleEntry("trusted_func", ModuleEnd)))),
           [Den("untrusted_val"); Den("trusted_func")])
  ) in

  (* Test 12: Try to execute trusted function with untrusted argument *)
  print_test_header "Test_12: Try to execute trusted function with untrusted argument";
  execWithFailure(
    Let("trusted_func",
        TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
        Let("untrusted_val", EInt(42),
            Apply(Den("trusted_func"), Den("untrusted_val"))))
  );

  (* Test 13: Successful trusted function call with trusted argument *)
  print_test_header "Test_13: Successful trusted function call with trusted argument";
  let _ = execWithSuccess(
    Let("trusted_func",
        TrustFun(make_signature [make_param "x" Trust] Trust, Sum(Den("x"), EInt(1))),
        TrustLet("trusted_val", Trust, EInt(42),
                Apply(Den("trusted_func"), Den("trusted_val"))))
  ) in

    (* Test 14: Try to promote untrusted function to trusted - should fail *)
  print_test_header "Test_14: Try to promote untrusted function to trusted via TrustLet";
  execWithFailure(
      Let("untrusted_func", Fun("x", Den("x")),
          TrustLet("trusted_func", Trust, Den("untrusted_func"),
                  Den("trusted_func")))
  );

  (* Test 15: Try to promote untrusted recursive function to trusted - should fail *)
  print_test_header "Test_15: Try to promote untrusted recursive function to trusted via TrustLet";
  execWithFailure(
      Letrec("factorial", "n",
            IfThenElse(IsZero(Den("n")), 
                      EInt(1), 
                      Prod(Den("n"), Apply(Den("factorial"), Diff(Den("n"), EInt(1))))),
            TrustLet("trusted_factorial", Trust, Den("factorial"),
                    Den("trusted_factorial")))
  );

  (* Test 16: Untrusted function with trusted input should return untrusted result *)
  print_test_header "Test_16: Untrusted function processing trusted data returns untrusted result";
  let result = execWithSuccess(
      Let("untrusted_func", Fun("x", Den("x")), (* identity function *)
          TrustLet("trusted_data", Trust, EInt(42),
                  Apply(Den("untrusted_func"), Den("trusted_data"))))
  ) in
  (* Verify the result is untrusted *)
  let trust_level = getTrustLevel result in
  if trust_level = Untrust then
      Printf.printf "✓ PASS: Result correctly downgraded to untrusted\n"
  else
      Printf.printf "✗ FAIL: Result should be untrusted but got trusted\n";

  (* Test 17: Untrusted function doing computation on trusted data returns untrusted result *)
  print_test_header "Test_17: Untrusted function computation on trusted data returns untrusted result";
  let result = execWithSuccess(
      Let("untrusted_func", Fun("x", Sum(Den("x"), EInt(10))), (* add 10 *)
          TrustLet("trusted_data", Trust, EInt(5),
                  Apply(Den("untrusted_func"), Den("trusted_data"))))
  ) in
  (* Verify the result is untrusted even though computation was on trusted data *)
  let _ = getTrustLevel result in
  match result with
  | Int(value, trust) ->
      if value = 15 && trust = Untrust then
          Printf.printf "✓ PASS: Computation result (15) correctly downgraded to untrusted\n"
      else
          Printf.printf "✗ FAIL: Expected Int(15, Untrust) but got Int(%d, %s)\n" 
                      value (if trust = Trust then "Trust" else "Untrust")
  | _ -> Printf.printf "✗ FAIL: Expected Int result\n";

  (* Test 18: Trusted function with trusted data still returns trusted result *)
  print_test_header "Test_18: Trusted function with trusted data returns trusted result";
  let result = execWithSuccess(
      Let("trusted_func",
          TrustFun(make_signature [make_param "x" Trust] Trust, Sum(Den("x"), EInt(1))),
          TrustLet("trusted_data", Trust, EInt(41),
                  Apply(Den("trusted_func"), Den("trusted_data"))))
  ) in
  let _ = getTrustLevel result in
  match result with
  | Int(value, trust) ->
      if value = 42 && trust = Trust then
          Printf.printf "✓ PASS: Trusted function result (42) remains trusted\n"
      else
          Printf.printf "✗ FAIL: Expected Int(42, Trust) but got Int(%d, %s)\n" 
                      value (if trust = Trust then "Trust" else "Untrust")
  | _ -> Printf.printf "✗ FAIL: Expected Int result\n";

  (* Test 19: Verify TrustLet can still promote data values to trusted *)
  print_test_header "Test_19: TrustLet can still promote data values to trusted";
  let result = execWithSuccess(
      Let("untrusted_int", EInt(100),
          TrustLet("trusted_int", Trust, Den("untrusted_int"),
                  Den("trusted_int")))
  ) in
  let _ = getTrustLevel result in
  match result with
  | Int(value, trust) ->
      if value = 100 && trust = Trust then
          Printf.printf "✓ PASS: Data value (100) correctly promoted to trusted\n"
      else
          Printf.printf "✗ FAIL: Expected Int(100, Trust) but got Int(%d, %s)\n" 
                      value (if trust = Trust then "Trust" else "Untrust")
  | _ -> Printf.printf "✗ FAIL: Expected Int result\n";

  (* Test 20: Complex scenario - untrusted function in trusted context *)
  print_test_header "Test_20: Complex scenario - untrusted function processing trusted data in chain";
  let result = execWithSuccess(
      Let("untrusted_double", Fun("x", Prod(Den("x"), EInt(2))),
          Let("untrusted_add_one", Fun("y", Sum(Den("y"), EInt(1))),
              TrustLet("trusted_data", Trust, EInt(5),
                      Apply(Den("untrusted_add_one"), 
                            Apply(Den("untrusted_double"), Den("trusted_data"))))))
  ) in
  let _ = getTrustLevel result in
  match result with
  | Int(value, trust) ->
      if value = 11 && trust = Untrust then
          Printf.printf "✓ PASS: Chain computation (5*2+1=11) correctly results in untrusted\n"
      else
          Printf.printf "✗ FAIL: Expected Int(11, Untrust) but got Int(%d, %s)\n" 
                      value (if trust = Trust then "Trust" else "Untrust")
  | _ -> Printf.printf "✗ FAIL: Expected Int result\n";

  (* Test 21: Verify that already trusted functions can be "promoted" (no-op) *)
  print_test_header "Test_21: Already trusted function can be promoted (no-op)";
  let result = execWithSuccess(
      Let("trusted_func",
          TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
          TrustLet("still_trusted_func", Trust, Den("trusted_func"),
                  TrustLet("trusted_input", Trust, EInt(99),
                          Apply(Den("still_trusted_func"), Den("trusted_input")))))
  ) in
  let _ = getTrustLevel result in
  match result with
  | Int(value, trust) ->
      if value = 99 && trust = Trust then
          Printf.printf "✓ PASS: Already trusted function promotion is no-op, result remains trusted\n"
      else
          Printf.printf "✗ FAIL: Expected Int(99, Trust) but got Int(%d, %s)\n" 
                      value (if trust = Trust then "Trust" else "Untrust")
  | _ -> Printf.printf "✗ FAIL: Expected Int result\n";

  (* Test 14: String operations with trust propagation *)
  print_test_header "Test_14: String operations with trust propagation";
  let _ = execWithSuccess(
    TrustLet("trusted_str", Trust, EString("hello"),
             Let("untrusted_str", EString("world"),
                 StrContains(Den("trusted_str"), Den("untrusted_str"))))
  ) in

  (* Test 15: Recursive function with trust *)
  print_test_header "Test_15: Recursive function with trust";
  let _ = execWithSuccess(
    Letrec("factorial", "n",
           IfThenElse(IsZero(Den("n")),
                     EInt(1),
                     Prod(Den("n"), Apply(Den("factorial"), Diff(Den("n"), EInt(1))))),
           Apply(Den("factorial"), EInt(5)))
  ) in

  (* Test 16: Module function access from outside plugin (allowed) *)
  print_test_header "Test_16: Module function access from outside plugin (allowed)";
  let _ = execWithSuccess(
    Let("trusted_module",
        Module("SafeMath",
               ModuleLet("safe_add", Trust,
                        TrustFun(make_signature [make_param "x" Trust] Trust,
                                Sum(Den("x"), EInt(10))),
                        ModuleEntry("safe_add", ModuleEnd)),
               [Den("safe_add")]),
        TrustLet("input", Trust, EInt(5),
                Apply(ModuleAccess(Den("trusted_module"), "safe_add"), Den("input"))))
  ) in

  (* Test 17: Prevent module function leakage through variables in plugin *)
  print_test_header "Test_17: Prevent module function leakage through variables in plugin";
  execWithFailure(
    Let("trusted_module",
        Module("CryptoMath",
               ModuleLet("encrypt", Trust,
                        TrustFun(make_signature [make_param "data" Trust] Trust, Den("data")),
                        ModuleEntry("encrypt", ModuleEnd)),
               [Den("encrypt")]),
        Let("leaked_func", ModuleAccess(Den("trusted_module"), "encrypt"),
            Let("plugin", Include(EInt(1)),
                Execute(Den("plugin"), Den("leaked_func"), EInt(42)))))
  );

  (* Test 18: Untrusted module functions can be used in plugins *)
  print_test_header "Test_18: Untrusted module functions can be used in plugins";
  let _ = execWithSuccess(
    Let("untrusted_module",
        Module("UntrustedMath",
               ModuleLet("simple_add", Untrust,
                        Fun("x", Sum(Den("x"), EInt(1))),
                        ModuleEntry("simple_add", ModuleEnd)),
               [Den("simple_add")]),
        Let("plugin", Include(EInt(1)),
            Execute(Den("plugin"), 
                   ModuleAccess(Den("untrusted_module"), "simple_add"), 
                   EInt(5))))
  ) in

  (* Test 19: Custom validation with ValidateWith *)
  print_test_header "Test_19: ValidateWith using custom trusted predicate function";
  (* Define a trusted validation function that accepts only strings with "ok" inside *)
  let _ = execWithSuccess(
    Let("trusted_module",
        Module("ValidatorModule",
               ModuleLet("validate_str", Trust,
                        TrustFun(make_signature [make_param "s" Untrust] Trust,
                                 StrContains(Den("s"), EString("ok"))),
                        ModuleEntry("validate_str", ModuleEnd)),
               [Den("validate_str")]),
        (* Use module entry point for validation *)
        Let("input", EString("message_ok"),
            Let("res_fn", ModuleAccess(Den("trusted_module"), "validate_str"),
                Let("good", ValidateWith(Den("res_fn"), Den("input")),
                    Assert("good", Trust)))))
  ) in
  (* Test 20: Failure case for ValidateWith predicate *)
  print_test_header "Test_20: ValidateWith with predicate failure";
  execWithFailure(
    Let("trusted_module",
        Module("ValidatorModuleFail",
               ModuleLet("validate_num", Trust,
                        TrustFun(make_signature [make_param "x" Untrust] Trust,
                                 Eq(Den("x"), EInt(1))),
                        ModuleEntry("validate_num", ModuleEnd)),
               [Den("validate_num")]),
        (* Attempt with incorrect argument *)
        Let("res_fn", ModuleAccess(Den("trusted_module"), "validate_num"),
            ValidateWith(Den("res_fn"), EInt(2))))
  );

  (* Test 21: Include/Execute chaining with nested plugins *)
  print_test_header "Test_21: Nested plugin chaining";
  (* Inner plugin computes 2 + 3 *)
  let _ = execWithSuccess(
    Let("inner", Include(Sum(EInt(2), EInt(3))),
        Let("outer", Include(Den("inner")),
            Execute(Den("outer"), Fun("x", Sum(Den("x"), EInt(10))), EInt(5))))
  ) in

  print_separator();
  Printf.printf "\n=== ALL SECURITY TESTS COMPLETED ===\n\n"

(* If you want to run directly *)
let () = 
  if !Sys.interactive then ()
  else run_security_suite ()