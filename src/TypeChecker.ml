open Ast
open Core.Std

type typ =
  (** Non-empty set of types that this value may have. *)
  | UnionOf of simple_typ BatSet.t

let (wrap : simple_typ BatSet.t -> typ) stypes =
  let () = assert (not (BatSet.is_empty stypes)) in
  UnionOf stypes

let (wrap_one : simple_typ -> typ) stype =
  wrap (BatSet.singleton stype)

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

let (typ_equal : typ -> typ -> bool) t1 t2 =
  BatSet.equal (unwrap t1) (unwrap t2)

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

let (call_status_to_string : call_status -> string) call_status =
  Sexp.to_string (sexp_of_call_status call_status)

let (call_status_equal : call_status -> call_status -> bool) s1 s2 =
  match (s1, s2) with
    | (Executing, s2) -> s2 = Executing
    | (Suspended, s2) -> s2 = Suspended
    | (CompletedWithResult r1, CompletedWithResult r2) -> typ_equal r1 r2
    | (CompletedWithResult r1, _) -> false
    | (NeverCompletes, s2) -> s2 = NeverCompletes

(** Interpreter state while executing statements in a program. *)
type exec_context = {
  (** Program that is being executed. *)
  program : program;
  (** Whether debug output should be generated *)
  debug : bool;
  
  (** List of functions that were invoked to reach the current function,
    * including the current function itself. Current function is listed first.
    * Immediate caller is listed second. Further callers listed next. *)
  call_stack : frame list;
  (** Set of local variables, and the type of value each one currently holds.
    * When entering a new function starts with the function parameters only. *)
  names : (string, typ) BatMap.t;
  (** Within a function, whether the current block is still executing and isn't
    * suspended due to abrupt termination (via a return) or inability to make
    * progress on a function call. When entering a new function starts true.
    * 
    * When returning from a function call, whether the caller should continue
    * execution. If false then the caller should be suspended because the
    * callee did not have enough information to generate a return type. *)
  executing : bool;
  
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

let (log : string -> exec_context -> unit) message context =
  if context.debug then
    printf "* %s: %s\n" message (Sexp.to_string (sexp_of_exec_context context))
  else
    ()

let (log_raw : string -> exec_context -> unit) message context =
  if context.debug then
    printf "%s" message
  else
    ()

let rec
  (exec : exec_context -> stmt -> exec_context) context stmt =
    if not context.executing then
      context
    else
      match stmt with
        | AssignLiteral { target_var = target_var; literal = literal } ->
          let () = log "assign" context in
          let literal_typ = wrap_one literal in
          let after_assign_context = {
            context with
            names = BatMap.add target_var literal_typ context.names
          } in
          after_assign_context
          
        | AssignCall { target_var = target_var; func_name = func_name; arg_var = arg_var } ->
          let func = find_func context.program.funcs func_name in
          let arg_value = BatMap.find arg_var context.names in
          
          (* NOTE: Captures: func_name, context *)
          let log_call message =
            (log (sprintf "%s '%s'" message func_name) context) in
          
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
                  | Executing ->
                    (* A (non-ancestor) sibling function shouldn't still
                     * be executing... *)
                    assert false
                    
                  | Suspended ->
                    (* Perform an optimizing-suspension *)
                    let () = log_call "call#cached#skip" in
                    
                    let suspended_context = {
                      context with 
                      executing = false;
                      has_optimize_suspended_call = true
                    } in
                    suspended_context
                  
                  | CompletedWithResult result_type ->
                    (* Use the cached return type *)
                    let () = log_call "call#cached#continue" in
                        
                    let exit_func_context = {
                      context with
                      returned_types = unwrap result_type
                    } in
                    finish exit_func_context
                  
                  | NeverCompletes ->
                    (* Never completes? Suspend execution *)
                    let () = log_call "call#cached#neverreturn" in
                        
                    let suspended_context = {
                      context with
                      executing = false;
                      completes = false
                    } in
                    suspended_context
              else
                (* Non-recursive call *)
                let () = log_call "call#nonrec" in
                
                let exit_func_context = exec_func context func arg_value in
                finish exit_func_context
            
            | Some prior_frame_with_func ->
              (* Recursive call *)
              (match prior_frame_with_func.approx_return_type with
                | ReturnsAtLeast approx_return_type ->
                  (* Use the approx return type as the result and continue *)
                  let () = log_call "call#rec#resume" in
                  
                  let resumed_context = {
                    context with
                    names = BatMap.add target_var approx_return_type context.names
                  } in
                  resumed_context
                
                | ReturnsBeingCalculated ->
                  (* No approx return type available yet? Suspend execution *)
                  let () = log_call "call#rec#suspend" in
                  
                  let suspended_context = {
                    context with 
                    executing = false;
                    targets_of_recursion_suspended_calls = 
                      BatSet.add func context.targets_of_recursion_suspended_calls
                  } in
                  suspended_context
                
                | NeverReturns ->
                  (* Never completes? Suspend execution *)
                  let () = log_call "call#rec#neverreturn" in
                  
                  let suspended_context = {
                    context with
                    executing = false;
                    completes = false
                  } in
                  suspended_context
              )
          )
        
        | If { then_block = then_block; else_block = else_block } ->
          let () = log_raw "* if\n" context in
          let if_context = context in
          
          let then_context = if_context in
          let () = log "then" then_context in
          let end_then_context = exec_list then_context then_block in
          let () = log "end then" end_then_context in
          
          let else_context = {
            end_then_context with
            executing = if_context.executing; (* i.e. true *)
            names = if_context.names
          } in
          let () = log "else" else_context in
          let end_else_context = exec_list else_context else_block in
          let () = log "end else" end_else_context in
          
          let (join : typ -> typ -> typ) typ1 typ2 = 
            match (typ1, typ2) with
              | (UnionOf stypes1, UnionOf stypes2) ->
                UnionOf (BatSet.union stypes1 stypes2)
            in
          
          let end_if_context = {
            program = context.program;
            debug = context.debug;
            call_stack = context.call_stack;
            names = BatMap.intersect
              join
              end_then_context.names
              end_else_context.names;
            executing = 
              end_then_context.executing || 
              end_else_context.executing;
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
            cached_calls = end_else_context.cached_calls
          } in
          let () = log "end if" end_if_context in
          end_if_context
        
        | Return { result_var = result_var } ->
          let () = log "return" context in
          let result_typ = BatMap.find result_var context.names in
          let returning_context = {
            context with
            executing = false;
            returned_types = 
              BatSet.union (unwrap result_typ) context.returned_types
          } in
          returning_context
    and
  
  (exec_list : exec_context -> stmt list -> exec_context) context stmt_list =
    BatList.fold_left exec context stmt_list
    and
  
  (exec_func : exec_context -> func -> typ -> exec_context) context func arg_value =
    let () = log_raw "\n" context in
    
    let enter_func_context = {
      context with
      names = BatMap.of_enum (BatList.enum [(func.param_var, arg_value)]);
      executing = true;
      returned_types = BatSet.empty;
      targets_of_recursion_suspended_calls = BatSet.empty;
      has_optimize_suspended_call = false
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
    let () = log (sprintf "func '%s'" func.name) context in
    let step1 = exec_list context func.body in
    (* TODO: Rename to returned_context *)
    let step2 =
      if step1.executing then
        (* Implicit return of NoneType at the end of a function's body *)
        let returning_context = {
          step1 with
          executing = false;
          returned_types = BatSet.add NoneType step1.returned_types
        } in
        returning_context
      else
        step1
      in
    let () = log (sprintf "end func '%s'" func.name) step2 in
    let () = log_raw "\n" step2 in
    
    let (finish : exec_context -> func -> bool -> call_status -> exec_context)
        context func executing call_status =
      let exit_func_context = {
        context with
        call_stack = BatList.tl context.call_stack;
        executing = executing;
        targets_of_recursion_suspended_calls = 
          BatSet.remove func context.targets_of_recursion_suspended_calls;
        cached_calls = BatMap.add (func, arg_value) call_status context.cached_calls
      } in
      exit_func_context
      in
    
    (* TODO: The next two if-statements, which try to deduce the termination
     *       possiblities for the function, are quite brittle.
     * 
     *       Would be great to represent termination information in
     *       exec_context in a more explicit way so that this code
     *       can be rewritten in a more obvious fashion. *)
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
  
  (exec_program : ?debug:bool -> program -> exec_context) ?(debug=false) program =
    let main_func = 
      match program.funcs with
        | (head :: _) ->
          head
        
        | [] ->
          raise ProgramHasNoMainFunction
      in
    let initial_context = {
      program = program;
      debug = debug;
      call_stack = [];
      names = BatMap.empty;
      executing = true;
      returned_types = BatSet.empty;
      targets_of_recursion_suspended_calls = BatSet.empty;
      has_optimize_suspended_call = false;
      completes = true;
      cached_calls = BatMap.empty
    } in
    exec_func initial_context main_func (wrap_one NoneType)
