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

let print_section_header section_name =
  Printf.printf "\n=== %s ===\n" section_name

(* Helper functions for creating trust signatures and parameters *)
let make_param name trust_level = {param_name = name; param_trust = trust_level}
let make_signature params return_trust = {params = params; return_trust = return_trust}

(* Main security tests *)
let run_security_suite () =
  Printf.printf "\n TrustLang security tests \n\n";

  print_section_header "Trust primitive testing";

  (* Basic binding discipline *)
  print_test_header "Test_1: Let + Fun → Valid (Untrusted function binding)";
  let _ = execWithSuccess(
      Let("untrusted_func", Fun("x", Sum(Den("x"), EInt(1))),
          Apply(Den("untrusted_func"), EInt(5)))
  ) in

  print_test_header "Test_2: Let + TrustFun → Security error";
  execWithFailure(
      Let("should_fail", TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
          Den("should_fail"))
  );

  print_test_header "Test_3: TrustLet + Fun → Security error";
  execWithFailure(
      TrustLet("should_fail", Fun("x", Den("x")),
              Den("should_fail"))
  );

  print_test_header "Test_4: TrustLet + TrustFun → Valid (Trusted function binding)";
  let _ = execWithSuccess(
      TrustLet("trusted_func",
               TrustFun(make_signature [make_param "x" Trust] Trust, Sum(Den("x"), EInt(1))),
               TrustLet("trusted_input", EInt(41),
                       Apply(Den("trusted_func"), Den("trusted_input"))))
  ) in

  print_test_header "Test_5: Let cannot bind validated (trusted) data";
  execWithFailure(
      Let("validated_data", Validate(EInt(42)),
          Den("validated_data"))
  );

  (* TrustLet validation *)
  print_test_header "Test_6: TrustLet validates safe data during binding";
  let _ = execWithSuccess(
      TrustLet("trusted_int", EInt(100),
              Assert("trusted_int", Trust))
  ) in

  print_test_header "Test_7: TrustLet fails with unsafe string content";
  execWithFailure(
      TrustLet("trusted_str", EString("unsafe$content"),
              Den("trusted_str"))
  );

  print_test_header "Test_8: TrustLet fails with negative integer";
  execWithFailure(
      TrustLet("trusted_int", EInt(-5),
              Den("trusted_int"))
  );

  (* Validate primitives *)
  print_test_header "Test_9: Validate promotes untrusted data to trusted";
  let _ = execWithSuccess(
      Let("untrusted_str", EString("hello"),
          TrustLet("trusted_str", Validate(Den("untrusted_str")),
                  Assert("trusted_str", Trust)))
  ) in

  print_test_header "Test_10: Cannot validate already trusted data";
  execWithFailure(
    TrustLet("trusted_val", EInt(42),
            Validate(Den("trusted_val")))
  );

  print_test_header "Test_12: ValidateWith using trusted predicate";
  let _ = execWithSuccess(
      TrustLet("validator",
               TrustFun(make_signature [make_param "s" Untrust] Trust,
                       StrContains(Den("s"), EString("ok"))),
               Let("untrusted_input", EString("message_ok"),
                   TrustLet("validated_input", ValidateWith(Den("validator"), Den("untrusted_input")),
                           Assert("validated_input", Trust))))
  ) in

  print_test_header "Test_13: ValidateWith with predicate failure";
  execWithFailure(
    TrustLet("validator",
             TrustFun(make_signature [make_param "x" Untrust] Trust,
                     Eq(Den("x"), EInt(1))),
             ValidateWith(Den("validator"), EInt(2)))
  );

  print_test_header "Test_14: ValidateWith with already trusted data (no-op)";
  let _ = execWithSuccess(
    TrustLet("validator",
             TrustFun(make_signature [make_param "s" Untrust] Trust, CstTrue),
             TrustLet("trusted_data", EString("test"),
                     ValidateWith(Den("validator"), Den("trusted_data"))))
  ) in

  (* Function application trust rules *)
  print_test_header "Test_15: Trusted function with trusted argument";
  let _ = execWithSuccess(
    TrustLet("trusted_func",
             TrustFun(make_signature [make_param "x" Trust] Trust, Sum(Den("x"), EInt(1))),
             TrustLet("trusted_val", EInt(42),
                     Apply(Den("trusted_func"), Den("trusted_val"))))
  ) in

  print_test_header "Test_16: Trusted function with untrusted argument → Security error";
  execWithFailure(
    TrustLet("trusted_func",
             TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
             Let("untrusted_val", EInt(42),
                 Apply(Den("trusted_func"), Den("untrusted_val"))))
  );

  print_test_header "Test_17: Untrusted function with trusted data → Untrusted result";
  let _ = execWithSuccess(
      Let("untrusted_func", Fun("x", Den("x")),
          TrustLet("trusted_data", EInt(42),
                  Apply(Den("untrusted_func"), Den("trusted_data"))))
  ) in

  (* Trust assertions *)
  print_test_header "Test_18: Trust assertion success";
  let _ = execWithSuccess(
    TrustLet("trusted_val", EInt(42),
            Assert("trusted_val", Trust))
  ) in

  print_test_header "Test_19: Trust assertion failure";
  execWithFailure(
    Let("untrusted_val", EInt(42),
        Assert("untrusted_val", Trust))
  );

  (* Pattern matching *)
  print_test_header "Test_20: Pattern matching with trusted values";
  let _ = execWithSuccess(
    TrustLet("trusted_num", EInt(5),
            Match(Den("trusted_num"), 
                  [(PConst(EInt(5)), EString("matched"));
                   (PWildcard, EString("no match"))]))
  ) in

  (* Recursive functions *)
  print_test_header "Test_21: Untrusted recursive function with Letrec";
  let _ = execWithSuccess(
    Let("factorial", 
        Letrec("fact", "n",
              IfThenElse(IsZero(Den("n")), 
                        EInt(1), 
                        Prod(Den("n"), Apply(Den("fact"), Diff(Den("n"), EInt(1))))),
              Den("fact")),
        Apply(Den("factorial"), EInt(3)))
  ) in

  print_section_header "MODULES";

  (* Module binding discipline *)
  print_test_header "Test_22: ModuleLet + Fun → Valid";
  let _ = execWithSuccess(
    Let("untrusted_module",
        Module("UntrustedModule",
               ModuleLet("untrusted_func",
                        Fun("x", Sum(Den("x"), EInt(1))),
                        ModuleEntry("untrusted_func", ModuleEnd)),
               [Den("untrusted_func")]),
        Apply(ModuleAccess(Den("untrusted_module"), "untrusted_func"), EInt(5)))
  ) in

  print_test_header "Test_23: ModuleLet + TrustFun → Security error";
  execWithFailure(
    Module("TestModule",
           ModuleLet("should_fail", 
                    TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
                    ModuleEnd),
           [])
  );

  print_test_header "Test_24: ModuleTrustLet + Fun → Security error";
  execWithFailure(
    Module("TestModule",
           ModuleTrustLet("should_fail", 
                         Fun("x", Den("x")),
                         ModuleEnd),
           [])
  );

  print_test_header "Test_25: ModuleTrustLet + TrustFun → Valid";
  let _ = execWithSuccess(
    TrustLet("trusted_module",
        Module("TrustedModule", 
               ModuleTrustLet("trusted_func", 
                             TrustFun(make_signature [make_param "x" Trust] Trust,
                                     Sum(Den("x"), EInt(1))),
                             ModuleEntry("trusted_func", ModuleEnd)),
               [Den("trusted_func")]),
        TrustLet("input", EInt(5),
                Apply(ModuleAccess(Den("trusted_module"), "trusted_func"), Den("input"))))
  ) in

  (* Module data binding *)
  print_test_header "Test_26: ModuleLet binds untrusted data";
  let _ = execWithSuccess(
    Let("data_module",
        Module("DataModule",
               ModuleLet("untrusted_data", EInt(42),
                        ModuleEntry("untrusted_data", ModuleEnd)),
               [Den("untrusted_data")]),
        ModuleAccess(Den("data_module"), "untrusted_data"))
  ) in

  print_test_header "Test_27: ModuleTrustLet validates and binds trusted data";
  let _ = execWithSuccess(
    TrustLet("trusted_data_module",
        Module("TrustedDataModule",
               ModuleTrustLet("trusted_data", EString("safe"),
                             ModuleEntry("trusted_data", ModuleEnd)),
               [Den("trusted_data")]),
        ModuleAccess(Den("trusted_data_module"), "trusted_data"))
  ) in

  print_test_header "Test_28: ModuleTrustLet fails with unsafe data";
  execWithFailure(
    Module("UnsafeDataModule",
           ModuleTrustLet("unsafe_data", EString("unsafe$content"),
                         ModuleEnd),
           [])
  );

  (* Module access control *)
  print_test_header "Test_29: Try to access non-entry point method";
  execWithFailure(
    TrustLet("trusted_module",
        Module("TrustedMath",
               ModuleTrustLet("secret_func",
                             TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
                             ModuleTrustLet("public_func",
                                           TrustFun(make_signature [make_param "x" Trust] Trust, Den("x")),
                                           ModuleEntry("public_func", ModuleEnd))),
               [Den("public_func")]),
        ModuleAccess(Den("trusted_module"), "secret_func"))
  );

  (* Complex modules *)
  print_test_header "Test_30: Complex module with mixed trust levels";
  let _ = execWithSuccess(
    Let("mixed_module",
        Module("MixedModule",
               ModuleLet("untrusted_val", EInt(10),
                        ModuleTrustLet("trusted_func",
                                      TrustFun(make_signature [make_param "x" Untrust] Trust,
                                              Sum(Den("x"), EInt(1))),
                                      ModuleEntry("untrusted_val",
                                                 ModuleEntry("trusted_func", ModuleEnd)))),
               [Den("untrusted_val"); Den("trusted_func")]),
        ModuleAccess(Den("mixed_module"), "untrusted_val"))
  ) in

  (* Trusted vs Untrusted module binding *)
  print_test_header "Test_31: Let cannot bind trusted module";
  execWithFailure(
    Let("trusted_module",
        Module("TrustedMath",
               ModuleTrustLet("trusted_add",
                             TrustFun(make_signature [make_param "x" Trust] Trust, Sum(Den("x"), EInt(1))),
                             ModuleEntry("trusted_add", ModuleEnd)),
               [Den("trusted_add")]),
        ModuleAccess(Den("trusted_module"), "trusted_add"))
  );

  print_test_header "Test_32: TrustLet cannot bind untrusted module";
  execWithFailure(
    TrustLet("untrusted_module",
        Module("UntrustedMath",
               ModuleLet("untrusted_add",
                        Fun("x", Sum(Den("x"), EInt(1))),
                        ModuleEntry("untrusted_add", ModuleEnd)),
               [Den("untrusted_add")]),
        ModuleAccess(Den("untrusted_module"), "untrusted_add"))
  );

  print_section_header "PLUGINS";

  (* Basic plugin execution *)
  print_test_header "Test_33: Plugin execution with safe untrusted code";
  let _ = execWithSuccess(
    Let("plugin",
        Include(Sum(EInt(5), EInt(10))),
        Let("safe_func", Fun("x", Sum(Den("x"), EInt(1))),
            Execute(Den("plugin"), Den("safe_func"), EInt(42))))
  ) in

  (* Plugin security violations *)
  print_test_header "Test_34: Try to pass trusted function to plugin";
  execWithFailure(
    TrustLet("trusted_module",
        Module("TrustedMath",
               ModuleTrustLet("trusted_add",
                             TrustFun(make_signature [make_param "x" Trust; make_param "y" Trust] Trust,
                                     Sum(Den("x"), Den("y"))),
                             ModuleEntry("trusted_add", ModuleEnd)),
               [Den("trusted_add")]),
        Let("plugin", Include(EInt(42)),
            Execute(Den("plugin"), 
                   ModuleAccess(Den("trusted_module"), "trusted_add"), 
                   EInt(5))))
  );

  print_test_header "Test_35: Try to use trusted module function inside plugin definition";
  execWithFailure(
    TrustLet("trusted_module",
        Module("TrustedMath",
               ModuleTrustLet("trusted_multiply",
                             TrustFun(make_signature [make_param "x" Trust; make_param "y" Trust] Trust,
                                     Prod(Den("x"), Den("y"))),
                             ModuleEntry("trusted_multiply", ModuleEnd)),
               [Den("trusted_multiply")]),
        Let("malicious_plugin",
            Include(Apply(ModuleAccess(Den("trusted_module"), "trusted_multiply"), EInt(5))),
            Execute(Den("malicious_plugin"), Fun("x", Den("x")), EInt(1))))
  );

  print_test_header "Test_36: Prevent function leakage through variables in plugin";
  execWithFailure(
    TrustLet("trusted_module",
        Module("CryptoMath",
               ModuleTrustLet("encrypt",
                             TrustFun(make_signature [make_param "data" Trust] Trust, Den("data")),
                             ModuleEntry("encrypt", ModuleEnd)),
               [Den("encrypt")]),
        Let("leaked_func", ModuleAccess(Den("trusted_module"), "encrypt"),
            Let("plugin", Include(EInt(1)),
                Execute(Den("plugin"), Den("leaked_func"), EInt(42)))))
  );

  (* Safe plugin operations *)
  print_test_header "Test_37: Untrusted module functions can be used in plugins";
  let _ = execWithSuccess(
    Let("untrusted_module",
        Module("UntrustedMath",
               ModuleLet("simple_add",
                        Fun("x", Sum(Den("x"), EInt(1))),
                        ModuleEntry("simple_add", ModuleEnd)),
               [Den("simple_add")]),
        Let("plugin", Include(EInt(1)),
            Execute(Den("plugin"), 
                   ModuleAccess(Den("untrusted_module"), "simple_add"), 
                   EInt(5))))
  ) in

  print_test_header "Test_38: Plugin with conditional computation";
  let _ = execWithSuccess(
    Let("plugin", Include(Prod(EInt(6), EInt(7))),
        Let("compute_func", Fun("x", 
            IfThenElse(GreaterThan(Den("x"), EInt(40)),
                      EString("large"),
                      EString("small"))),
            Execute(Den("plugin"), Den("compute_func"), EInt(30))))
  ) in

  print_test_header "Test_39: Try to execute trusted recursive function in plugin";
  execWithFailure(
    TrustLet("trusted_factorial",
             TrustFun(make_signature [make_param "n" Trust] Trust,
                     IfThenElse(IsZero(Den("n")), EInt(1), 
                               Prod(Den("n"), Apply(Den("trusted_factorial"), Diff(Den("n"), EInt(1)))))),
             Let("plugin", Include(EInt(1)),
                 Execute(Den("plugin"), Den("trusted_factorial"), EInt(5))))
  );

  print_separator();
  Printf.printf "\n=== ALL SECURITY TESTS COMPLETED ===\n\n"

let () = 
  if !Sys.interactive then ()
  else run_security_suite ()