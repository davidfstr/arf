open Ast
open Core.Std

type exec_context = {
  program : program;
  (* Current function is listed first. Immediate caller is listed second. *)
  call_stack : func list;
  names : (string, typ) BatMap.t;
  returned_types : typ BatSet.t;
  suspended_via_call_to : func BatSet.t;
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
          if not (BatList.mem func context.call_stack) then
            (* Non-recursive call *)
            let () = printf "* call#nonrec: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
            let arg_value = BatMap.find arg_var context.names in
            let enter_func_context = {
              context with
              call_stack = func :: context.call_stack;
              names = BatMap.of_enum (BatList.enum [(func.param_var, arg_value)]);
              returned_types = BatSet.empty;
              suspended_via_call_to = BatSet.empty;
              executing = true
            } in
            let exit_func_context = exec_func enter_func_context func in
            (* TODO: Handle functions that can return multiple kinds of values *)
            let returned_value = unique_item exit_func_context.returned_types in
            let resumed_context = {
              context with
              names = BatMap.add target_var returned_value context.names
            } in
            resumed_context
          else
            (* Recursive call *)
            let () = printf "* call#rec: %s\n" (Sexp.to_string (sexp_of_exec_context context)) in
            (* TODO: If named func has approx return type then use it,
             *       rather than *always* suspending here *)
            let suspended_context = {
              context with 
              suspended_via_call_to = BatSet.add func context.suspended_via_call_to;
              executing = false
            } in
            suspended_context
        
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
              | _ -> NoneType (* TODO: Support union types *)
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
    let final_context = exec_list context func.body in
    if final_context.executing then
      (* Implicit return of NoneType at the end of a function's body *)
      let returning_context = {
        final_context with
        returned_types = BatSet.add NoneType final_context.returned_types;
        executing = false
      } in
      returning_context
    else
      final_context
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
      call_stack = [main_func];
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

let output = exec_program input4
let () = printf "%s\n" (Sexp.to_string (sexp_of_exec_context output))
