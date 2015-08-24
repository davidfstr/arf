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
  (** Whether the current function contains a call that performed
    * an optimizing-suspension. *)
  has_optimize_suspended_call : bool;
  (** Whether the current function completes along any execution path,
    * including abrupt termination (via a return). *)
  completes : bool;
  
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
  List [
    List [Atom f.name; sexp_of_typ t];
    sexp_of_call_status cs
  ]

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
              (* Non-recursive call, possibly cached *)
              
              let (finish : exec_context -> exec_context) exit_func_context =
                if exit_func_context.executing then
                  let returned_typ = wrap exit_func_context.returned_types in
                  
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
                (* Cached call *)
                match BatMap.find (func, arg_value) context.cached_calls with
                  | Executing
                  | Suspended ->
                    (* Perform an optimizing-suspension *)
                    let () = printf "* call#cached#skip: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                    
                    let suspended_context = {
                      context with 
                      has_optimize_suspended_call = true;
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
                    finish exit_func_context
                  
                  | NeverCompletes ->
                    (* Never returns? Suspend execution *)
                    let () = printf "* call#cached#neverreturn: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                        
                    let suspended_context = {
                      context with
                      completes = false;
                      executing = false
                    } in
                    suspended_context
              else
                (* Non-recursive call *)
                let () = printf "* call#nonrec: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                
                let exit_func_context = exec_func context func arg_value in
                finish exit_func_context
            
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
                    completes = false;
                    executing = false
                  } in
                  suspended_context
              )
          )
        
        | If { then_block = then_block; else_block = else_block } ->
          let () = printf "* if\n" in
          let if_context = context in
          
          let then_context = if_context in
          let () = printf "* then: %s\n" (Sexp.to_string (sexp_of_exec_context then_context)) in
          let end_then_context = exec_list then_context then_block in
          let () = printf "* end then: %s\n" (Sexp.to_string (sexp_of_exec_context end_then_context)) in
          
          let else_context = {
            end_then_context with
            names = if_context.names;
            executing = if_context.executing (* i.e. true *)
          } in
          let () = printf "* else: %s\n" (Sexp.to_string (sexp_of_exec_context else_context)) in
          let end_else_context = exec_list else_context else_block in
          let () = printf "* end else: %s\n" (Sexp.to_string (sexp_of_exec_context end_else_context)) in
          
          let (join : typ -> typ -> typ) typ1 typ2 = 
            match (typ1, typ2) with
              | (UnionOf stypes1, UnionOf stypes2) ->
                UnionOf (BatSet.union stypes1 stypes2)
            in
          
          let end_if_context = {
            program = context.program;
            call_stack = context.call_stack;
            names = BatMap.intersect
              join
              end_then_context.names
              end_else_context.names;
            returned_types = BatSet.union
              end_then_context.returned_types
              end_else_context.returned_types;
            targets_of_recursion_suspended_calls = BatSet.union
              end_then_context.targets_of_recursion_suspended_calls
              end_else_context.targets_of_recursion_suspended_calls;
            has_optimize_suspended_call = 
              end_then_context.has_optimize_suspended_call || 
              end_else_context.has_optimize_suspended_call;
            completes =
              end_then_context.completes ||
              end_else_context.completes;
            executing = 
              end_then_context.executing || 
              end_else_context.executing;
            cached_calls = end_else_context.cached_calls
          } in
          let () = printf "* end if: %s\n" (Sexp.to_string (sexp_of_exec_context end_if_context)) in
          end_if_context
        
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
  
  (exec_func : exec_context -> func -> typ -> exec_context) context func arg_value =
    let () = printf "\n" in
    
    let enter_func_context = {
      context with
      names = BatMap.of_enum (BatList.enum [(func.param_var, arg_value)]);
      returned_types = BatSet.empty;
      targets_of_recursion_suspended_calls = BatSet.empty;
      has_optimize_suspended_call = false;
      executing = true
    } in
    exec_func_body enter_func_context func ReturnsBeingCalculated Executing
    and
  
  (exec_func_body : exec_context -> func -> func_return_typ -> call_status -> exec_context)
      step0 func approx_return_type call_status =
    let arg_value = BatMap.find func.param_var step0.names in
    
    (* TODO: Rename to step1.5 or similar *)
    let new_frame = { func = func; approx_return_type = approx_return_type } in
    let context = {
      step0 with 
      call_stack = new_frame :: step0.call_stack;
      cached_calls = BatMap.add (func, arg_value) call_status step0.cached_calls
    } in
    
    (* Execute the function *)
    let () = printf "* func '%s': %s\n" func.name (Sexp.to_string (sexp_of_exec_context context)) in
    let step1 = exec_list context func.body in
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
    let () = printf "\n" in
    
    let (finish : exec_context -> func -> bool -> call_status -> exec_context)
        context func executing call_status =
      let exit_func_context = {
        context with
        call_stack = BatList.tl context.call_stack;
        targets_of_recursion_suspended_calls = 
          BatSet.remove func context.targets_of_recursion_suspended_calls;
        executing = executing;
        cached_calls = BatMap.add (func, arg_value) call_status context.cached_calls
      } in
      exit_func_context
      in
    
    if not step2.completes then
      finish step2 func false NeverCompletes
    else
      let was_not_suspended = 
        (BatSet.is_empty step2.targets_of_recursion_suspended_calls) &&
        (not step2.has_optimize_suspended_call) in
      (if was_not_suspended then
        (* Body was not suspended anywhere,
         * so we can return an exact return type to our caller *)
        
        finish step2 func true (CompletedWithResult (wrap step2.returned_types))
      
      else
        (* Body was suspended due to either
         * (1) a recursive call to self, an ancestor function,
         *     or some combination; or
         * (2) an optimizing suspension. *)
        
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
              exec_func_body step0 func NeverReturns NeverCompletes
              
            else
              (* ...and may be able to compute a better approx return type
               * later because an ancestor caller is being depended on. *)
              
              (* Suspend execution of self within caller *)
              finish step2 func false Suspended
            )
          else
            (* Improve approx return type of self and reexecute body *)
            exec_func_body step0 func (ReturnsAtLeast (wrap step2.returned_types)) Executing
          
        else
          (* If body was suspended due to either
           *    (1) a recursive call to ancestors only or
           *    (2) an optimizing suspension,
           * suspend execution of self within caller *)
          finish step2 func false Suspended
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
    let initial_context = {
      program = program;
      call_stack = [];
      names = BatMap.empty;
      returned_types = BatSet.empty;
      targets_of_recursion_suspended_calls = BatSet.empty;
      has_optimize_suspended_call = false;
      completes = true;
      executing = true;
      cached_calls = BatMap.empty
    } in
    exec_func initial_context main_func (wrap (BatSet.singleton NoneType))

(* -------------------------------------------------------------------------- *)
(* Tests *)

(* Program: Returns main's argument, namely NoneType. *)
let test_return_arg = {
  funcs = [
    {
      name = "main"; param_var = "_"; body = [
        Return { result_var = "_" };
      ]
    }
  ]
}

(* Program: Returns the literal Int. *)
let test_return_literal = {
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
let test_call_identity = {
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
let test_self_recursion = {
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

(* Program: Computes is_even and is_odd with mutual recursion *)
let test_mutual_recursion = {
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
            AssignLiteral { target_var = "k"; literal = Int };
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
            AssignLiteral { target_var = "k"; literal = Int };
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
}

(* Program: Call self in infinite loop.
 * Ensure type checker doesn't get caught in an infinite loop itself. *)
let test_self_infinite_loop = {
  funcs = [
    {
      name = "infinite_loop"; param_var = "_"; body = [
        AssignCall { target_var = "_"; func_name = "infinite_loop"; arg_var = "_" };
        Return { result_var = "_" };
      ]
    }
  ]
}

(* Program: Call group of functions in infinite loop.
 * Ensure type checker doesn't get caught in an infinite loop itself. *)
let test_mutual_infinite_loop = {
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
}

(* Program: Return either an Int or a Bool.
 * Ensure type checker recognizes that a function can return multiple types. *)
let test_return_union_type = {
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
let deep_func_chain first_func_body last_func_body = [
  { name = "f1"; param_var = "_"; body = first_func_body };
  (* FIXME: Reinstate prior behavior *)
  { name = "f2"; param_var = "_"; body = if_then_call_else_call "f32" (*"f3"*) };
  (*
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
  *)
  (* TODO: See whether having f32 call f1 makes a difference in performance *)
  (* TODO: See whether having f1..32 call f1 makes a difference in performance *)
  (* TODO: See whether having f1..32 call f1..32 makes a difference in performance *)
  { name = "f32"; param_var = "_"; body = last_func_body };
]
let test_deep_call_chain = {
  funcs = deep_func_chain
    (if_then_call_else_call "f2")
    []
}

(* Program: Deep call chain of interlinked functions,
 *          where last function calls first function,
 *          and first function may return a constant.
 * Ensure type checker can evaluate in linear time rather than exponential. *)
let return_nothing = [Return { result_var = "_" }]
let test_deep_call_chain_with_cycle = {
  funcs = deep_func_chain
    [
      If {
        then_block = call "f2";
        else_block = return_nothing
      };
    ]
    (call "f1")
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

(* -------------------------------------------------------------------------- *)
(* Main *)

let output = exec_program test_mutual_infinite_loop
let () = printf "%s\n" (Sexp.to_string (sexp_of_exec_context output))
