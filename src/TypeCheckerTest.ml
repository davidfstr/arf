open Ast
open OUnit
open TypeChecker

(* -------------------------------------------------------------------------- *)
(* Utilities *)

exception NoUniqueStatusForFunc of string

let (inferred_return_status : exec_context -> string -> call_status)
    output func_name =
  let func = TypeChecker.find_func output.program.funcs func_name in
  let func_to_statuses = BatMap.filter
    (fun (f,p) s -> f = func)
    output.cached_calls in
  let statuses = BatList.of_enum (BatMap.values func_to_statuses) in
  match statuses with
    | [status] -> status
    | _ -> raise (NoUniqueStatusForFunc func_name)

let (inferred_return_status_in_context : exec_context -> string -> typ -> call_status)
    output func_name arg_typ =
  let func = TypeChecker.find_func output.program.funcs func_name in
  let func_to_statuses = BatMap.filter
    (fun (f,p) s -> (f = func) && (typ_equal p arg_typ))
    output.cached_calls in
  let statuses = BatList.of_enum (BatMap.values func_to_statuses) in
  match statuses with
    | [status] -> status
    | _ -> raise (NoUniqueStatusForFunc func_name)

let (assert_call_status_equals : exec_context -> string -> call_status -> unit)
    output func_name call_status =
  assert_equal ~cmp:call_status_equal ~printer:call_status_to_string
    call_status (inferred_return_status output func_name)

let (assert_return_type_equals : exec_context -> string -> typ -> unit)
    output func_name return_type =
  assert_call_status_equals output func_name (CompletedWithResult return_type)

let (assert_return_type_equals_just : exec_context -> string -> simple_typ -> unit)
    output func_name return_type =
  assert_return_type_equals output func_name (wrap_one return_type)

let (assert_return_type_equals_one_of : exec_context -> string -> simple_typ list -> unit)
    output func_name return_types =
  assert_return_type_equals output func_name (wrap (BatSet.of_list return_types))

let (assert_return_type_equals_in_context : exec_context -> string -> simple_typ list -> simple_typ list -> unit)
    output func_name arg_types return_types =
  let arg_typ = wrap (BatSet.of_list arg_types) in
  let return_type = wrap (BatSet.of_list return_types) in
  let call_status = CompletedWithResult return_type in
  assert_equal ~cmp:call_status_equal ~printer:call_status_to_string
    call_status (inferred_return_status_in_context output func_name arg_typ)
  

(* -------------------------------------------------------------------------- *)
(* Tests *)

let tests = [
  (* Program: Returns main's argument, namely NoneType. *)
  "test_return_arg" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "main"; param_var = "_"; body = [
            Return { result_var = "_" };
          ]
        }
      ]
    } in
    assert_return_type_equals_just output "main" NoneType;
  );
  
  (* Program: Returns the literal Int. *)
  "test_return_literal" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "main"; param_var = "_"; body = [
            AssignLiteral { target_var = "k"; literal = Int };
            Return { result_var = "k" };
          ]
        }
      ]
    } in
    assert_return_type_equals_just output "main" Int;
  );
  
  (* Program: Calls f with main's argument. f returns its argument. *)
  "test_call_identity" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "main"; param_var = "_"; body = [
            AssignLiteral { target_var = "x"; literal = Int };
            AssignCall { target_var = "result"; func_name = "identity"; arg_var = "x" };
            Return { result_var = "result" };
          ]
        };
        {
          name = "identity"; param_var = "n"; body = [
            Return { result_var = "n" };
          ]
        };
      ]
    } in
    assert_return_type_equals_just output "main" Int;
    assert_return_type_equals_just output "identity" Int;
  );
  
  (* Program: Computes factorial recursively. *)
  "test_self_recursion" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "main"; param_var = "_"; body = [
            AssignLiteral { target_var = "k"; literal = Int };
            AssignCall { target_var = "result"; func_name = "fact"; arg_var = "k" };
            Return { result_var = "result" };
          ]
        };
        {
          name = "fact"; param_var = "n"; body = [
            If {
              then_block = [
                AssignLiteral { target_var = "k"; literal = Int };
                Return { result_var = "k" };
              ];
              else_block = [
                AssignCall { target_var = "result"; func_name = "fact"; arg_var = "n" };
                Return { result_var = "result" };
              ]
            };
          ]
        };
      ]
    } in
    assert_return_type_equals_just output "main" Int;
    assert_return_type_equals_just output "fact" Int;
  );
  
  (* Program: Computes is_even and is_odd with mutual recursion *)
  "test_mutual_recursion" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "main"; param_var = "_"; body = [
            AssignLiteral { target_var = "k"; literal = Int };
            AssignCall { target_var = "result"; func_name = "is_even"; arg_var = "k" };
            Return { result_var = "result" };
          ]
        };
        {
          name = "is_even"; param_var = "n"; body = [
            If {
              then_block = [
                AssignLiteral { target_var = "k"; literal = Bool };
                Return { result_var = "k" };
              ];
              else_block = [
                AssignCall { target_var = "result"; func_name = "is_odd"; arg_var = "n" };
                Return { result_var = "result" };
              ]
            };
          ]
        };
        {
          name = "is_odd"; param_var = "n"; body = [
            If {
              then_block = [
                AssignLiteral { target_var = "k"; literal = Bool };
                Return { result_var = "k" };
              ];
              else_block = [
                AssignCall { target_var = "result"; func_name = "is_even"; arg_var = "n" };
                Return { result_var = "result" };
              ]
            };
          ]
        };
      ]
    } in
    assert_return_type_equals_just output "main" Bool;
    assert_return_type_equals_just output "is_even" Bool;
    assert_return_type_equals_just output "is_odd" Bool;
  );
  
  (* Ensure that value from nested return propagates to calling function
   * in the presence of mutual recursion. *)
  "test_mutual_recursion_with_nested_return" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "f"; param_var = "_"; body = [
            AssignCall { target_var = "result"; func_name = "g"; arg_var = "_" };
            Return { result_var = "result" };
          ]
        };
        {
          name = "g"; param_var = "_"; body = [
            If {
              then_block = [
                AssignCall { target_var = "_"; func_name = "f"; arg_var = "_" };
                Return { result_var = "_" };
              ];
              else_block = [
                AssignLiteral { target_var = "k"; literal = Int };
                Return { result_var = "k" };
              ]
            };
          ]
        };
      ]
    } in
    assert_return_type_equals_just output "f" Int;
    assert_return_type_equals_just output "g" Int;
  );
  
  (* Program: Call self in infinite loop.
   * Ensure type checker doesn't get caught in an infinite loop itself. *)
  "test_self_infinite_loop" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "infinite_loop"; param_var = "_"; body = [
            AssignCall { target_var = "_"; func_name = "infinite_loop"; arg_var = "_" };
            Return { result_var = "_" };
          ]
        }
      ]
    } in
    assert_call_status_equals output "infinite_loop" NeverCompletes;
  );
  
  (* Program: Call group of functions in infinite loop.
   * Ensure type checker doesn't get caught in an infinite loop itself. *)
  "test_mutual_infinite_loop" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "infinite_loop_1"; param_var = "_"; body = [
            AssignCall { target_var = "_"; func_name = "infinite_loop_2"; arg_var = "_" };
            Return { result_var = "_" };
          ]
        };
        {
          name = "infinite_loop_2"; param_var = "_"; body = [
            AssignCall { target_var = "_"; func_name = "infinite_loop_1"; arg_var = "_" };
            Return { result_var = "_" };
          ]
        }
      ]
    } in
    assert_call_status_equals output "infinite_loop_1" NeverCompletes;
    assert_call_status_equals output "infinite_loop_2" NeverCompletes;
  );
  
  (* Program: Return either an Int or a Bool.
   * Ensure type checker recognizes that a function can return multiple types. *)
  "test_return_union_type" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "returns_int_or_bool"; param_var = "_"; body = [
            If {
              then_block = [
                AssignLiteral { target_var = "k"; literal = Int };
                Return { result_var = "k" };
              ];
              else_block = [
                AssignLiteral { target_var = "k"; literal = Bool };
                Return { result_var = "k" };
              ]
            };
          ]
        }
      ]
    } in
    assert_return_type_equals_one_of output "returns_int_or_bool" [Int; Bool];
  );
]

let call func_name = [
  AssignCall { target_var = "_"; func_name = func_name; arg_var = "_" };
  Return { result_var = "_" };
]
let if_then_call_else_call func_name = [
  If {
    then_block = call func_name;
    else_block = call func_name
  };
]
let return_nothing = [
  Return { result_var = "_" }
]
let deep_func_chain first_func_body last_func_body = [
  { name = "f1"; param_var = "_"; body = first_func_body };
  { name = "f2"; param_var = "_"; body = if_then_call_else_call "f3" };
  { name = "f3"; param_var = "_"; body = if_then_call_else_call "f4" };
  { name = "f4"; param_var = "_"; body = if_then_call_else_call "f5" };
  { name = "f5"; param_var = "_"; body = if_then_call_else_call "f6" };
  { name = "f6"; param_var = "_"; body = if_then_call_else_call "f7" };
  { name = "f7"; param_var = "_"; body = if_then_call_else_call "f8" };
  { name = "f8"; param_var = "_"; body = if_then_call_else_call "f9" };
  { name = "f9"; param_var = "_"; body = if_then_call_else_call "f10" };
  { name = "f10"; param_var = "_"; body = if_then_call_else_call "f11" };
  { name = "f11"; param_var = "_"; body = if_then_call_else_call "f12" };
  { name = "f12"; param_var = "_"; body = if_then_call_else_call "f13" };
  { name = "f13"; param_var = "_"; body = if_then_call_else_call "f14" };
  { name = "f14"; param_var = "_"; body = if_then_call_else_call "f15" };
  { name = "f15"; param_var = "_"; body = if_then_call_else_call "f16" };
  { name = "f16"; param_var = "_"; body = if_then_call_else_call "f17" };
  { name = "f17"; param_var = "_"; body = if_then_call_else_call "f18" };
  { name = "f18"; param_var = "_"; body = if_then_call_else_call "f19" };
  { name = "f19"; param_var = "_"; body = if_then_call_else_call "f20" };
  { name = "f20"; param_var = "_"; body = if_then_call_else_call "f21" };
  { name = "f21"; param_var = "_"; body = if_then_call_else_call "f22" };
  { name = "f22"; param_var = "_"; body = if_then_call_else_call "f23" };
  { name = "f23"; param_var = "_"; body = if_then_call_else_call "f24" };
  { name = "f24"; param_var = "_"; body = if_then_call_else_call "f25" };
  { name = "f25"; param_var = "_"; body = if_then_call_else_call "f26" };
  { name = "f26"; param_var = "_"; body = if_then_call_else_call "f27" };
  { name = "f27"; param_var = "_"; body = if_then_call_else_call "f28" };
  { name = "f28"; param_var = "_"; body = if_then_call_else_call "f29" };
  { name = "f29"; param_var = "_"; body = if_then_call_else_call "f30" };
  { name = "f30"; param_var = "_"; body = if_then_call_else_call "f31" };
  { name = "f31"; param_var = "_"; body = if_then_call_else_call "f32" };
  (* TODO: See whether having f32 call f1 makes a difference in performance *)
  (* TODO: See whether having f1..32 call f1 makes a difference in performance *)
  (* TODO: See whether having f1..32 call f1..32 makes a difference in performance *)
  { name = "f32"; param_var = "_"; body = last_func_body };
]

let tests = tests @ [
  (* Program: Deep call chain of interlinked functions.
   * Ensure type checker can evaluate in linear time rather than exponential. *)
  "test_deep_call_chain" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = deep_func_chain
        (if_then_call_else_call "f2")
        []
    } in
    assert_return_type_equals_just output "f1" NoneType;
    assert_return_type_equals_just output "f2" NoneType;
    assert_return_type_equals_just output "f31" NoneType;
    assert_return_type_equals_just output "f32" NoneType;
  );
  
  (* Program: Deep call chain of interlinked functions,
   *          where last function calls first function,
   *          and first function may return a constant.
   * Ensure type checker can evaluate in linear time rather than exponential. *)
  "test_deep_call_chain_with_cycle" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = deep_func_chain
        [
          If {
            then_block = call "f2";
            else_block = return_nothing
          };
        ]
        (call "f1")
    } in
    assert_return_type_equals_just output "f1" NoneType;
    assert_return_type_equals_just output "f2" NoneType;
    assert_return_type_equals_just output "f31" NoneType;
    assert_return_type_equals_just output "f32" NoneType;
  );
  
  (* See whether having f1 call both f2#Int and f2#Bool, where f2 is the
   * identity function, deduces the correct type for f2 in both cases,
   * in the presence of optimizations. *)
  "test_call_identity_in_multiple_contexts" >:: ( fun () ->
    let output = TypeChecker.exec_program {
      funcs = [
        {
          name = "main"; param_var = "_"; body = [
            If {
              then_block = [
                AssignLiteral { target_var = "x"; literal = Int };
                AssignCall { target_var = "result"; func_name = "identity"; arg_var = "x" };
                AssignCall { target_var = "result"; func_name = "expects_int"; arg_var = "result" };
                Return { result_var = "result" };
              ];
              else_block = [
                AssignLiteral { target_var = "x"; literal = Bool };
                AssignCall { target_var = "result"; func_name = "identity"; arg_var = "x" };
                AssignCall { target_var = "result"; func_name = "expects_bool"; arg_var = "result" };
                Return { result_var = "result" };
              ]
            }
          ]
        };
        {
          name = "identity"; param_var = "n"; body = [
            Return { result_var = "n" };
          ]
        };
        {
          name = "expects_int"; param_var = "n"; body = [
            Return { result_var = "n" };
          ]
        };
        {
          name = "expects_bool"; param_var = "n"; body = [
            Return { result_var = "n" };
          ]
        };
      ]
    } in
    assert_return_type_equals_in_context output "identity" [Int] [Int];
    assert_return_type_equals_in_context output "identity" [Bool] [Bool];
    assert_return_type_equals_just output "expects_int" Int;
    assert_return_type_equals_just output "expects_bool" Bool;
  );
]

let rec call_fi_to_fn i n =
  if i < n then
    [
      If {
        then_block = call ("f" ^ (string_of_int i));
        else_block = call_fi_to_fn (i + 1) n
      }
    ]
  else (* i = n *)
    call ("f" ^ (string_of_int n))
let rec range min max =
  if min < max then
    min :: (range (min + 1) max)
  else (* min = max *)
    [min]
let deep_func_chain_all_pairs n with_return = 
  let fi i = {
    name = "f" ^ (string_of_int i);
    param_var = "_";
    body = 
      if with_return && (i = n) then
        (* The last function additionally returns nothing *)
        [
          If {
            then_block = call_fi_to_fn 1 n;
            else_block = return_nothing
          }
        ]
      else
        call_fi_to_fn 1 n
        
  } in
  BatList.map fi (range 1 n)

let tests = tests @ [
  (* Program: Deep call chain of functions, where every function calls
   *          every other function.
   * Ensure type checker can evaluate in linear time rather than exponential. *)
  "test_deep_call_chain_all_pairs_with_no_returns" >:: ( fun () ->
    let n = 32 in
    let output = TypeChecker.exec_program {
      funcs = deep_func_chain_all_pairs n false
    } in
    let rec check i n call_status =
      assert_call_status_equals output ("f" ^ (string_of_int i)) call_status;
      if i < n then
        check (i + 1) n call_status
      else
        ()
      in
    check 1 n NeverCompletes
  );
  
  (* TODO: Make this test pass with large n. Breaks somewhere in 10-15 range. *)
  (*
  (* Program: Deep call chain of functions, where every function calls
   *          every other function.
   * Ensure type checker can evaluate in quadratic time rather than exponential. *)
  "test_deep_call_chain_all_pairs_with_one_return" >:: ( fun () ->
    let n = 32 in
    let output = TypeChecker.exec_program ~debug:true {
      funcs = deep_func_chain_all_pairs n true
    } in
    let rec check i n call_status =
      assert_call_status_equals output ("f" ^ (string_of_int i)) call_status;
      if i < n then
        check (i + 1) n call_status
      else
        ()
      in
    check 1 n (CompletedWithResult (wrap_one NoneType))
  );
  *)
]

let suite = "TypeCheckerTests" >::: tests

let _ =
  run_test_tt suite
