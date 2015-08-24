open Ast
open Core.Std

type typ =
  (** Non-empty set of types that this value may have. *)
  | UnionOf of simple_typ BatSet.t

let (wrap : simple_typ BatSet.t -> typ) stypes =
  let () = assert (not (BatSet.is_empty stypes)) in
  UnionOf stypes

let (unwrap : typ -> simple_typ BatSet.t) typ =
  match typ with
    | UnionOf stypes ->
      stypes

let (sexp_of_typ : typ -> Sexp.t) typ =
  let open Core.Std.Sexp in
  let stypes = unwrap typ in
  match BatSet.to_list stypes with
    | [] ->
      (* NOTE: This is not a valid state for a typ *)
      Atom "__empty__"
      
    | [unique_type] ->
      sexp_of_simple_typ unique_type
    
    | _ ->
      List [
        Atom "UnionOf";
        sexp_of_list sexp_of_simple_typ (BatSet.to_list stypes)
      ]

type func_return_typ =
  (** Return type that is in the process of being calculated,
    * since the function has not yet completed one full execution pass. *)
  | ReturnsBeingCalculated
  (** Approximate return type that may be at least one of the specified
    * simple types, but may be extended with additional simple types
    * on subsequent execution passes of the function. *)
  | ReturnsAtLeast of typ
  (** Special return type that indicates that the function
    * provably never terminates. *)
  | NeverReturns

type frame = {
  (** The function executing in this frame. *)
  func : func;
  (** Approximate return type of the function in this frame,
    * which may be extended while the function is still executing 
    * and computing its fix point. *)
  approx_return_type : func_return_typ
}

type call_status =
  | Executing
  | Suspended
  | CompletedWithResult of typ
  | NeverCompletes
  with sexp_of

(** Interpreter state while executing statements in a program. *)
type exec_context = {
  (** Program that is being executed. *)
  program : program;
  (** List of functions that were invoked to reach the current function,
    * including the current function itself. Current function is listed first.
    * Immediate caller is listed second. Further callers listed next. *)
  call_stack : frame list;
  (** Set of local variables, and the type of value each one currently holds.
    * When entering a new function starts with the function parameters only. *)
  names : (string, typ) BatMap.t;
  (** Within a function, the set of all simple types returned by various
    * return statements in function. When entering a new function starts empty.
    * 
    * When returning from a function call, the set of types that could be
    * returned from the callee. *)
  returned_types : simple_typ BatSet.t;
  (** Set of functions that could not be called recursively because they
    * had no return type information available yet. Is always a subset of the
    * functions in the current call stack. When entering a new function starts empty. *)
  targets_of_recursion_suspended_calls : func BatSet.t;
  (** Within a function, whether the current block is still executing and isn't
    * suspended due to abrupt termination (via a return) or inability to make
    * progress on a function call. When entering a new function starts true.
    * 
    * When returning from a function call, whether the caller should continue
    * execution. If false then the caller should be suspended because the
    * callee did not have enough information to generate a return type. *)
  executing : bool;
  (** Total set of calls that the interpreter is in the process of executing
    * or has finished executing. Tracked so that repeated calls to the same
    * function can be optimized away. *)
  cached_calls : ((func * typ), call_status) BatMap.t
}

let (sexp_of_string_typ : (string * typ) -> Sexp.t) binding =
  let open Core.Std.Sexp in
  let (k, v) = binding in
  List [Atom k; sexp_of_typ v]

let func_names func_list =
  BatList.map (fun f -> f.name) func_list

let (sexp_of_func_typ_call_status : ((func * typ) * call_status) -> Sexp.t) cached_call =
  let open Core.Std.Sexp in
  let ((f, t), cs) = cached_call in
  List [Atom f.name; sexp_of_typ t; sexp_of_call_status cs]

let sexp_of_exec_context context =
  let open Core.Std.Sexp in
  List [
    List [Atom "names"; sexp_of_list sexp_of_string_typ (BatMap.bindings context.names)];
    List [Atom "returned_types"; sexp_of_list sexp_of_simple_typ (BatSet.to_list context.returned_types)];
    List [Atom "targets_of_recursion_suspended_calls"; sexp_of_list sexp_of_string (func_names (BatSet.to_list context.targets_of_recursion_suspended_calls))];
    List [Atom "executing"; Atom (string_of_bool context.executing)];
    List [Atom "cached_calls"; sexp_of_list sexp_of_func_typ_call_status (BatMap.bindings context.cached_calls)];
  ]

exception NoSuchFunction of string

let rec (find_func : func list -> string -> func) func_list func_name =
  match func_list with
    | (head :: tail) ->
      if head.name = func_name then
        head
      else
        find_func tail func_name
    
    | [] ->
      raise (NoSuchFunction func_name)

exception SetHasNoUniqueElement

let unique_item set =
  match BatSet.to_list set with
    | [x] ->
      x
    | _ ->
      raise SetHasNoUniqueElement

exception ProgramHasNoMainFunction

let rec
  (exec : exec_context -> stmt -> exec_context) context stmt =
    if not context.executing then
      context
    else
      match stmt with
        | AssignLiteral { target_var = target_var; literal = literal } ->
          let () = printf "* assign: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
          let literal_typ = UnionOf (BatSet.singleton literal) in
          let after_assign_context = {
            context with
            names = BatMap.add target_var literal_typ context.names
          } in
          after_assign_context
          
        | AssignCall { target_var = target_var; func_name = func_name; arg_var = arg_var } ->
          let func = find_func context.program.funcs func_name in
          let arg_value = BatMap.find arg_var context.names in
          
          let (continue_with_call_result : exec_context -> exec_context) exit_func_context =
            if exit_func_context.executing then
              let returned_typ = UnionOf exit_func_context.returned_types in
              
              let resumed_context = {
                exit_func_context with
                names = BatMap.add target_var returned_typ exit_func_context.names
              } in
              resumed_context
            else
              let suspended_context = {
                exit_func_context with
                (* NOTE: Redundant, but I want to be explicit *)
                executing = false
              } in
              suspended_context
            in
          
          if BatMap.mem (func, arg_value) context.cached_calls then
            match BatMap.find (func, arg_value) context.cached_calls with
              | Executing
              | Suspended ->
                (* Perform an optimizing-suspension *)
                let () = printf "* call#cached#skip: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                
                let suspended_context = {
                  context with 
                  (* NOTE: This is a optimizing-suspension rather than a
                   *       recursion-suspension. Therefore we don't track
                   *       the call target. *)
                  (* NOTE: Redundant, but I want to be explicit *)
                  targets_of_recursion_suspended_calls = context.targets_of_recursion_suspended_calls;
                  executing = false
                } in
                suspended_context
              
              | CompletedWithResult result_type ->
                (* Use the cached return type *)
                let () = printf "* call#cached#continue: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                    
                let exit_func_context = {
                  context with
                  returned_types = unwrap result_type
                } in
                continue_with_call_result exit_func_context
              
              | NeverCompletes ->
                (* Never returns? Suspend execution *)
                let () = printf "* call#cached#neverreturn: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                    
                let suspended_context = {
                  context with
                  (* NOTE: Redundant, but I want to be explicit *)
                  targets_of_recursion_suspended_calls = context.targets_of_recursion_suspended_calls;
                  executing = false
                } in
                suspended_context
                
          else
            let rec (find_frame_with_func : frame list -> func -> frame option) frame_list func =
              match frame_list with
                | (head :: tail) ->
                  if head.func = func then
                    Some head
                  else
                    find_frame_with_func tail func
                
                | [] ->
                  None
              in
            
            (match find_frame_with_func context.call_stack func with
              | None ->
                (* Non-recursive call *)
                let () = printf "* call#nonrec: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                
                let new_frame = {
                  func = func;
                  approx_return_type = ReturnsBeingCalculated
                } in
                let enter_func_context = {
                  context with
                  call_stack = new_frame :: context.call_stack;
                  names = BatMap.of_enum (BatList.enum [(func.param_var, arg_value)]);
                  returned_types = BatSet.empty;
                  targets_of_recursion_suspended_calls = BatSet.empty;
                  executing = true;
                  cached_calls = BatMap.add (func, arg_value) Executing context.cached_calls
                } in
                
                let exit_func_context = exec_func enter_func_context func in
                continue_with_call_result exit_func_context
              
              | Some prior_frame_with_func ->
                (* Recursive call *)
                (match prior_frame_with_func.approx_return_type with
                  | ReturnsAtLeast approx_return_type ->
                    (* Use the approx return type as the result and continue *)
                    let () = printf "* call#rec#resume: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                    
                    let resumed_context = {
                      context with
                      names = BatMap.add target_var approx_return_type context.names
                    } in
                    resumed_context
                  
                  | ReturnsBeingCalculated ->
                    (* No approx return type available yet? Suspend execution *)
                    let () = printf "* call#rec#suspend: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                    
                    let suspended_context = {
                      context with 
                      targets_of_recursion_suspended_calls = BatSet.add func context.targets_of_recursion_suspended_calls;
                      executing = false
                    } in
                    suspended_context
                  
                  | NeverReturns ->
                    (* Never returns? Suspend execution *)
                    let () = printf "* call#rec#neverreturn: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                    
                    let suspended_context = {
                      context with
                      (* NOTE: Redundant, but I want to be explicit *)
                      targets_of_recursion_suspended_calls = context.targets_of_recursion_suspended_calls;
                      executing = false
                    } in
                    suspended_context
                )
            )
        
        | If { then_block = then_block; else_block = else_block } ->
          let () = printf "* if: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
          let () = printf "* then\n" in
          let then_result = exec_list context then_block in
          let () = printf "* end then: %s\n" (Sexp.to_string (sexp_of_exec_context then_result)) in
          let () = printf "* else\n" in
          let else_result = exec_list
            (* TODO: Almost certainly need to be taking more state from then_result... *)
            { context with cached_calls = then_result.cached_calls }
            else_block in
          let () = printf "* end else: %s\n" (Sexp.to_string (sexp_of_exec_context else_result)) in
          
          let (join : typ -> typ -> typ) typ1 typ2 = 
            match (typ1, typ2) with
              | (UnionOf stypes1, UnionOf stypes2) ->
                UnionOf (BatSet.union stypes1 stypes2)
            in
          
          let joined_result = {
            program = context.program;
            call_stack = context.call_stack;
            names = BatMap.intersect
              join
              then_result.names
              else_result.names;
            returned_types = BatSet.union
              then_result.returned_types
              else_result.returned_types;
            targets_of_recursion_suspended_calls = BatSet.union
              then_result.targets_of_recursion_suspended_calls
              else_result.targets_of_recursion_suspended_calls;
            executing = then_result.executing || else_result.executing;
            cached_calls = else_result.cached_calls
          } in
          let () = printf "* end if: %s\n" (Sexp.to_string (sexp_of_exec_context joined_result)) in
          joined_result
        
        | Return { result_var = result_var } ->
          let () = printf "* return: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
          let result_typ = BatMap.find result_var context.names in
          let returning_context = {
            context with
            returned_types = BatSet.union (unwrap result_typ) context.returned_types;
            executing = false
          } in
          returning_context
    and
  
  (exec_list : exec_context -> stmt list -> exec_context) context stmt_list =
    BatList.fold_left exec context stmt_list
    and
  
  (exec_func : exec_context -> func -> exec_context) context func =
    let arg_value = BatMap.find func.param_var context.names in
    
    (* Execute the function *)
    let () = printf "* func '%s': %s\n" func.name (Sexp.to_string (sexp_of_exec_context context)) in
    let step0 = context in
    let step1 = exec_list step0 func.body in
    (* TODO: Rename to returned_context *)
    let step2 =
      if step1.executing then
        (* Implicit return of NoneType at the end of a function's body *)
        let returning_context = {
          step1 with
          returned_types = BatSet.add NoneType step1.returned_types;
          executing = false
        } in
        returning_context
      else
        step1
      in
    let () = printf "* end func '%s': %s\n" func.name (Sexp.to_string (sexp_of_exec_context step2)) in
    
    (* TODO: Shouldn't this be checking step2.executing to be more reliable? *)
    (if BatSet.is_empty step2.targets_of_recursion_suspended_calls then
      (* Body was not suspended anywhere,
       * so we can return an exact return type to our caller *)
      
      let call_status = CompletedWithResult (wrap step2.returned_types) in
      let resumed_context = {
        step2 with
        (* NOTE: Redundant, but I want to be explicit *)
        returned_types = step2.returned_types;
        executing = true;
        cached_calls = BatMap.add (func, arg_value) call_status step2.cached_calls
      } in
      resumed_context
    
    else
      (* Body was suspended due to a recursive call to self,
       * an ancestor function, or some combination. *)
      
      (if BatSet.mem func step2.targets_of_recursion_suspended_calls then
        (* If body was suspended somewhere due to self,
         * try to compute a better approx return type for self and
         * reexecute the body *)
        
        if BatSet.is_empty step2.returned_types then
          (* Unable to compute an approx return type for self at the moment... *)
          (if (BatSet.to_list step2.targets_of_recursion_suspended_calls) = [func] then
            (* ...and will /never/ be able compute an approx return type
             * since no ancestor caller is being depended on.
             * 
             * The body is making a hard dependency on the return type
             * of self, but no further progress can be made in resolving
             * a return type for self. *)
            
            (* Force resolve approx return type of self to Unreachable
             * and reexecute body *)
            let new_frame = {
              func = func;
              approx_return_type = NeverReturns
            } in
            let step0_again = {
              step0 with
              call_stack = new_frame :: BatList.tl step2.call_stack
            } in
            exec_func step0_again func
            
          else
            (* ...and may be able to compute a better approx return type
             * later because an ancestor caller is being depended on. *)
            
            (* Suspend execution of self within caller *)
            let call_status = Suspended in
            let suspended_context = {
              step2 with
              targets_of_recursion_suspended_calls = BatSet.remove func step2.targets_of_recursion_suspended_calls;
              executing = false;
              cached_calls = BatMap.add (func, arg_value) call_status step2.cached_calls
            } in
            suspended_context
          )
        else
          (* Improve approx return type of self and reexecute body *)
          let new_frame = {
            func = func;
            approx_return_type = ReturnsAtLeast (wrap step2.returned_types)
          } in
          let step0_again = {
            step0 with
            call_stack = new_frame :: BatList.tl step2.call_stack
          } in
          exec_func step0_again func
        
      else
        (* If body was suspended due to ancestors only,
         * suspend execution of self within caller *)
        let call_status = Suspended in
        let suspended_context = {
          step2 with
          (* NOTE: This remove should be a no-op here. Leaving for consistency. *)
          targets_of_recursion_suspended_calls = BatSet.remove func step2.targets_of_recursion_suspended_calls;
          executing = false;
          cached_calls = BatMap.add (func, arg_value) call_status step2.cached_calls
        } in
        suspended_context
      )
    )
    and
  
  (exec_program : program -> exec_context) program =
    let main_func = 
      match program.funcs with
        | (head :: _) ->
          head
        
        | [] ->
          raise ProgramHasNoMainFunction
      in
    (* TODO: Try to inline computation of the inital context to exec_func,
     *       to avoid duplication with similar code in AssignCall. *)
    let initial_context = {
      program = program;
      call_stack = [{
        func = main_func;
        approx_return_type = ReturnsBeingCalculated
      }];
      names = BatMap.of_enum (BatList.enum [(
        main_func.param_var,
        wrap (BatSet.singleton NoneType)
      )]);
      returned_types = BatSet.empty;
      targets_of_recursion_suspended_calls = BatSet.empty;
      executing = true;
      cached_calls = BatMap.add (main_func, wrap (BatSet.singleton NoneType)) Executing BatMap.empty
    } in
    exec_func initial_context main_func

(* Program: Returns main's argument, namely NoneType. *)
let input1 = {
  funcs = [
    {
      name = "main"; param_var = "_"; body = [
        Return { result_var = "_" };
      ]
    }
  ]
}

(* Program: Returns the literal Int. *)
let input2 = {
  funcs = [
    {
      name = "main"; param_var = "_"; body = [
        AssignLiteral { target_var = "k"; literal = Int };
        Return { result_var = "k" };
      ]
    }
  ]
}

(* Program: Calls f with main's argument. f returns its argument. *)
let input3 = {
  funcs = [
    {
      name = "main"; param_var = "_"; body = [
        AssignLiteral { target_var = "x"; literal = Int };
        AssignCall { target_var = "result"; func_name = "f"; arg_var = "x" };
        Return { result_var = "result" };
      ]
    };
    {
      name = "f"; param_var = "n"; body = [
        Return { result_var = "n" };
      ]
    };
  ]
}

(* Program: Computes factorial recursively. *)
let input4 = {
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
}

(* Program: Call self in infinite loop.
 * Ensure type checker doesn't get caught in an infinite loop itself. *)
let input5 = {
  funcs = [
    {
      name = "infinite_loop"; param_var = "_"; body = [
        AssignCall { target_var = "_"; func_name = "infinite_loop"; arg_var = "_" };
        Return { result_var = "_" };
      ]
    }
  ]
}

(* Program: Return either an Int or a Bool.
 * Ensure type checker recognizes that a function can return multiple types. *)
let input6 = {
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
}

(* Program: Deep call chain of interlinked functions.
 * Ensure type checker can evaluate in linear time rather than exponential. *)
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
let input7 = {
  funcs = [
    { name = "f1"; param_var = "_"; body = if_then_call_else_call "f2" };
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
    { name = "f32"; param_var = "_"; body = [] };
  ]
}

(* TODO: See whether having f1 call both f2#Int and f2#Bool, where f2 is the
 *       identity function, deduces the correct type for f2 in both cases,
 *       in the presence of optimizations. *)

(* TODO: Ensure that an identity function when given type X returns only type X
 *       along a particular code path, even if the same identity function may
 *       be given type Y and return Y along a different path. In particular the
 *       identity function when given X should NOT return X|Y. *)

(* TODO: See whether having f1..32 call f1..32, with all possible argument types,
 *       makes a difference in performance *)

let output = exec_program input7
let () = printf "%s\n" (Sexp.to_string (sexp_of_exec_context output))
