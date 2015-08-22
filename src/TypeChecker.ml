open Ast
open Core.Std

type frame = {
  (** The function executing in this frame. *)
  func : func;
  (** Approximate return type of the function in this frame.
    * May be extended with additional union members while the function
    * is still executing and computing its fix point.
    * 
    * May be None if the function has not yet completed one full execution
    * pass and has no return type information available. *)
  approx_return_type : typ option
}

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
  (** Within a function, the set of all types returned by various
    * return statements in function. When entering a new function starts empty.
    * 
    * When returning from a function call, the set of types that could be
    * returned from the callee. *)
  returned_types : typ BatSet.t;
  (** Set of functions that could not be called recursively because they
    * had no return type information available yet. Is always a subset of the
    * functions in the current call stack. When entering a new function starts empty. *)
  suspended_via_call_to : func BatSet.t;  (* contains_suspensions_due_to *)
  (** Within a function, whether the current block is still executing and isn't
    * suspended due to abrupt termination (via a return) or inability to make
    * progress on a function call. When entering a new function starts true.
    * 
    * When returning from a function call, whether the caller should continue
    * execution. If false then the caller should be suspended because the
    * callee did not have enough information to generate a return type. *)
  executing : bool
}

let (sexp_of_string_typ : (string * typ) -> Sexp.t) binding =
  let open Core.Std.Sexp in
  let (k, v) = binding in
  List [Atom k; sexp_of_typ v]

let func_names func_list =
  BatList.map (fun f -> f.name) func_list

let sexp_of_exec_context context =
  let open Core.Std.Sexp in
  List [
    List [Atom "names"; sexp_of_list sexp_of_string_typ (BatMap.bindings context.names)];
    List [Atom "returned_types"; sexp_of_list sexp_of_typ (BatSet.to_list context.returned_types)];
    List [Atom "suspended_via_call_to"; sexp_of_list sexp_of_string (func_names (BatSet.to_list context.suspended_via_call_to))];
    List [Atom "executing"; Atom (string_of_bool context.executing)]
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
exception UnionTypesNotYetImplemented

let rec
  (exec : exec_context -> stmt -> exec_context) context stmt =
    if not context.executing then
      context
    else
      match stmt with
        | AssignLiteral { target_var = target_var; literal = literal } ->
          let () = printf "* assign: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
          let after_assign_context = {
            context with
            names = BatMap.add target_var literal context.names
          } in
          after_assign_context
          
        | AssignCall { target_var = target_var; func_name = func_name; arg_var = arg_var } ->
          let func = find_func context.program.funcs func_name in
          
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
              
              let arg_value = BatMap.find arg_var context.names in
              let new_frame = { func = func; approx_return_type = None } in
              let enter_func_context = {
                context with
                call_stack = new_frame :: context.call_stack;
                names = BatMap.of_enum (BatList.enum [(func.param_var, arg_value)]);
                returned_types = BatSet.empty;
                suspended_via_call_to = BatSet.empty;
                executing = true
              } in
              
              let exit_func_context = exec_func enter_func_context func in
              if exit_func_context.executing then
                (* TODO: Handle functions that can return multiple kinds of values *)
                let returned_value = unique_item exit_func_context.returned_types in
                
                let resumed_context = {
                  context with
                  names = BatMap.add target_var returned_value context.names
                } in
                resumed_context
              else
                let suspended_context = {
                  exit_func_context with
                  (* NOTE: Redundant, but I want to be explicit *)
                  executing = false
                } in
                suspended_context
            
            | Some prior_frame_with_func ->
              (* Recursive call *)
              (match prior_frame_with_func.approx_return_type with
                | Some approx_return_type ->
                  (* Use the approx return type as the result and continue *)
                  let () = printf "* call#rec#resume: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                  
                  let resumed_context = {
                    context with
                    names = BatMap.add target_var approx_return_type context.names
                  } in
                  resumed_context
                
                | None ->
                  (* No approx return type available yet? Suspend execution *)
                  let () = printf "* call#rec#suspend: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
                  
                  let suspended_context = {
                    context with 
                    suspended_via_call_to = BatSet.add func context.suspended_via_call_to;
                    executing = false
                  } in
                  suspended_context
              )
          )
        
        | If { then_block = then_block; else_block = else_block } ->
          let () = printf "* if: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
          let () = printf "* then\n" in
          let then_result = exec_list context then_block in
          let () = printf "* else\n" in
          let else_result = exec_list context else_block in
          
          let (join : typ -> typ -> typ) typ1 typ2 = 
            match (typ1, typ2) with
              | (NoneType, NoneType) -> NoneType
              | (Bool, Bool) -> Bool
              | (Int, Int) -> Int
              (* TODO: Support union types *)
              | _ -> raise UnionTypesNotYetImplemented
            in
          
          let () = printf "* end if\n" in
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
            suspended_via_call_to = BatSet.union
              then_result.suspended_via_call_to
              else_result.suspended_via_call_to;
            executing = then_result.executing || else_result.executing
          } in
          joined_result
        
        | Return { result_var = result_var } ->
          let () = printf "* return: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
          let result_value = BatMap.find result_var context.names in
          let returning_context = {
            context with
            returned_types = BatSet.add result_value context.returned_types;
            executing = false
          } in
          returning_context
    and
  
  (exec_list : exec_context -> stmt list -> exec_context) context stmt_list =
    BatList.fold_left exec context stmt_list
    and
  
  (exec_func : exec_context -> func -> exec_context) context func =
    (* Execute the function *)
    let step0 = context in
    let step1 = exec_list step0 func.body in
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
    
    (if BatSet.is_empty step2.suspended_via_call_to then
      (* Body was not suspended anywhere,
       * so we can return an exact return type to our caller *)
      
      let resumed_context = {
        step2 with
        (* NOTE: Redundant, but I want to be explicit *)
        returned_types = step2.returned_types;
        executing = true
      } in
      resumed_context
    
    else
      (* Body was suspended due to a recursive call to self,
       * an ancestor function, or some combination. *)
      
      (if BatSet.mem func step2.suspended_via_call_to then
        (* If body was suspended somewhere due to self,
         * try to compute a better approx return type for self and
         * reexecute the body *)
        
        match BatSet.to_list step2.returned_types with
          | [] -> 
            (* Unable to compute an approx return type for self at the moment... *)
            if (BatSet.to_list step2.suspended_via_call_to) = [func] then
              (* ...and will /never/ be able compute an approx return type
               * since no ancestor caller is being depended on.
               * 
               * The body is making a hard dependency on the return type
               * of self, but no further progress can be made in resolving
               * a return type for self. *)
              
              (* Force resolve approx return type of self to Unreachable
               * and reexecute body *)
              let new_frame = { func = func; approx_return_type = Some Unreachable } in
              let step0_again = {
                step0 with
                call_stack = new_frame :: BatList.tl step2.call_stack
              } in
              exec_func step0_again func
              
            else
              (* ...and may be able to compute a better approx return type
               * later because an ancestor caller is being depended on. *)
              
              (* Suspend execution of self within caller *)
              let suspended_context = {
                step2 with
                suspended_via_call_to = BatSet.remove func step2.suspended_via_call_to;
                executing = false
              } in
              suspended_context
          
          | [unique_return_type] ->
            (* Improve approx return type of self and reexecute body *)
            let new_frame = { func = func; approx_return_type = Some unique_return_type } in
            let step0_again = {
              step0 with
              call_stack = new_frame :: BatList.tl step2.call_stack
            } in
            exec_func step0_again func
            
          | _ ->
            raise UnionTypesNotYetImplemented (* TODO: Support union types *)
        
      else
        (* If body was suspended due to ancestors only,
         * suspend execution of self within caller *)
        let suspended_context = {
          step2 with
          (* NOTE: This remove should be a no-op here. Leaving for consistency. *)
          suspended_via_call_to = BatSet.remove func step2.suspended_via_call_to;
          executing = false
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
    let initial_context = {
      program = program;
      call_stack = [{ func = main_func; approx_return_type = None }];
      names = BatMap.of_enum (BatList.enum [(main_func.param_var, NoneType)]);
      returned_types = BatSet.empty;
      suspended_via_call_to = BatSet.empty;
      executing = true
    } in
    exec_func initial_context main_func

(* Program: Returns main's argument, namely NoneType. *)
let input1 = {
  funcs = [
    {
      name = "main"; param_var = "x"; body = [
        Return { result_var = "x" };
      ]
    }
  ]
}

(* Program: Returns the literal Int. *)
let input2 = {
  funcs = [
    {
      name = "main"; param_var = "x"; body = [
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
      name = "main"; param_var = "x"; body = [
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
      name = "main"; param_var = "x"; body = [
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

let input5 = {
  funcs = [
    {
      name = "infinite_loop"; param_var = "x"; body = [
        AssignCall { target_var = "x"; func_name = "infinite_loop"; arg_var = "x" };
        Return { result_var = "x" };
      ]
    }
  ]
}

let output = exec_program input5
let () = printf "%s\n" (Sexp.to_string (sexp_of_exec_context output))
