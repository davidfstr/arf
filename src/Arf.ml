open Ast
open Core.Std (* for Result.t, String.strip *)
open Printf

(* -------------------------------------------------------------------------- *)
(* Parse Errors *)

type parse_error =
  | IOError
  | ParseError of string

let parse_error_to_string error =
  match error with
    | IOError -> "I/O error"
    | ParseError message -> message

(* -------------------------------------------------------------------------- *)
(* Tokenizer *)

type
  token =
    | TDef of token_TDef
    | TIf
    | TAssignLiteral of token_TAssignLiteral
    | TAssignCall of token_TAssignCall
    | TReturn of token_TReturn
    | TElse
    | TPass
    and
  token_TDef = {
    name : string;
    param_var : string
  } and
  token_TAssignLiteral = {
    target_var : string;
    literal_type : simple_typ
  } and
  token_TAssignCall = {
    target_var : string;
    func_name : string;
    arg_var : string
  } and
  token_TReturn = {
    result_var : string
  }
  with sexp_of

let (token_to_string : token -> string) token =
  Sexp.to_string (sexp_of_token token)

let rec (tokenize : string list -> (token list, parse_error) Result.t) lines =
  match lines with
    | [] ->
      Ok []
    
    | (line :: next_lines) ->
      (* Strip # comment from line, if present *)
      let line =
        match String.index line '#' with
          | Some comment_offset -> String.sub line 0 comment_offset
          | None -> line
        in
      
      (* Strip whitespace on right *)
      let line = String.rstrip line in
      
      (* Strip whitespace on left, and measure indentation *)
      let (line_with_indent, line) = (line, String.lstrip line) in
      (* let indent = (String.length line_with_indent) - (String.length line) in *)
      
      if line = "" then
        (* Ignore blank lines *)
        tokenize next_lines
      else
        (* TODO: Don't repeatedly recompile these regexps *)
        (* NOTE: OCaml regexes use \( rather than ( for memory parentheses,
         *       unlike practically every other regex library. *)
        let iden = "\\([a-zA-Z_][a-zA-Z_0-9]*\\)" in
        let t_def_re = Str.regexp ("^def "^iden^"("^iden^"):$") in
        let t_assign_literal_re = Str.regexp ("^"^iden^" = <"^iden^">$") in
        let t_assign_call_re = Str.regexp ("^"^iden^" = "^iden^"("^iden^")$") in
        let t_return_re = Str.regexp ("^return "^iden^"$") in
        
        let (token_result : (token, parse_error) Result.t) =
          if Str.string_match t_def_re line 0 then
            let name = Str.matched_group 1 line in
            let param_var = Str.matched_group 2 line in
            Ok (TDef { name; param_var })
          
          else if Str.string_match t_assign_literal_re line 0 then
            let target_var = Str.matched_group 1 line in
            let literal_type_iden = Str.matched_group 2 line in
            (match 
              match literal_type_iden with
                | "NoneType" -> Some NoneType
                | "bool" -> Some Bool
                | "int" -> Some Int
                | _ -> None
            with
              | Some literal_type ->
                Ok (TAssignLiteral { target_var; literal_type })
              
              | None ->
                (* TODO: Emit parse error: unrecognized literal type *)
                Error (ParseError ("unrecognized literal type: " ^ literal_type_iden))
            )
          
          else if Str.string_match t_assign_call_re line 0 then
            let target_var = Str.matched_group 1 line in
            let func_name = Str.matched_group 2 line in
            let arg_var = Str.matched_group 3 line in
            Ok (TAssignCall { target_var; func_name; arg_var })
          
          else if Str.string_match t_return_re line 0 then
            let result_var = Str.matched_group 1 line in
            Ok (TReturn { result_var })
            
          else
            (* TODO: Emit parse error: unrecognized statement *)
            Error (ParseError ("line syntax not understood: " ^ line))
          in
        
        let open Result.Monad_infix in
        token_result >>= fun token ->
        tokenize next_lines >>= fun next_tokens ->
        Ok (token :: next_tokens)

(* -------------------------------------------------------------------------- *)
(* Parser *)

let rec (parse_stmt_list :
    ?allow_empty:bool -> token list -> ((stmt list * token list), parse_error) Result.t)
    ?(allow_empty=false) tokens =
  match tokens with
    | [] ->
      if allow_empty then
        Ok ([], [])
      else
        Error (ParseError "expected statement list but found EOF")
  
    | (token :: next_tokens) ->
      let stmt_option = match token with
        | TAssignLiteral { target_var; literal_type } ->
          Some (AssignLiteral { target_var; literal_type })
          
        | TAssignCall { target_var; func_name; arg_var } ->
          Some (AssignCall { target_var; func_name; arg_var })
          
        | TReturn { result_var } ->
          Some (Return { result_var })
          
        | TPass ->
          (* No-op *)
          None
          
        | _ ->
          (* Not a valid statement. Assume at end of statement list. *)
          None
        in
      
      match stmt_option with
        | Some stmt ->
          let open Result.Monad_infix in
          parse_stmt_list ~allow_empty:true next_tokens >>= fun (next_stmts, next_tokens) ->
          Ok (stmt :: next_stmts, next_tokens)
        
        | None ->
          Ok ([], token :: next_tokens)
          

let rec (parse_func_list : token list -> (func list, parse_error) Result.t) tokens =
  match tokens with
    | [] ->
      Ok []
    
    | TDef { name; param_var } :: next_tokens ->
      let open Result.Monad_infix in
      parse_stmt_list next_tokens >>= fun (body, next_tokens) ->
      parse_func_list next_tokens >>= fun next_funcs ->
      Ok ({ name; param_var; body } :: next_funcs)
    
    | other_token :: next_tokens ->
      Error (ParseError ("expected def statement but found: " ^ (token_to_string other_token)))

let (parse_funcs_from_lines : string list -> (func list, parse_error) Result.t) lines =
  let open Result.Monad_infix in
  tokenize lines >>= fun tokens ->
  parse_func_list tokens

let (parse_program_from_lines : string list -> (program, parse_error) Result.t) lines =
  let open Result.Monad_infix in
  parse_funcs_from_lines lines >>= fun funcs ->
  Ok { funcs = funcs }

let (read_lines_from_file_exn : string -> string list) filename =
  In_channel.with_file filename ~f:(fun file ->
    let lines = ref [] in
    try
      while true do
        lines := (input_line file) :: !lines
      done;
      assert false
    with
      | End_of_file ->
        BatList.rev !lines
  )

let (read_lines_from_file : string -> (string list, parse_error) Result.t) filename =
  try
    Ok (read_lines_from_file_exn filename)
  with
    (* TODO: Pass thru I/O error message, such as file not found *)
    | _ -> Error IOError

let (parse_program_from_file : string -> (program, parse_error) Result.t) filename =
  let open Result.Monad_infix in
  read_lines_from_file filename >>= fun lines -> 
  parse_program_from_lines lines

(* -------------------------------------------------------------------------- *)
(* print_return_types *)

let (print_return_types : TypeChecker.exec_context -> unit) output =
  printf "%s\n" (Sexp.to_string (TypeChecker.sexp_of_exec_context output))

(* -------------------------------------------------------------------------- *)
(* main *)

let (main : string array -> unit) args =
  match Array.to_list args with
    | [_; filename] ->
      (match parse_program_from_file filename with
        | Ok program ->
          let output = TypeChecker.exec_program program in
          print_return_types output
        
        | Error parse_error ->
          printf "%s\n" (parse_error_to_string parse_error);
          exit 1
      )
    
    | _ ->
      printf "syntax: Arf.native <filename>.arf\n";
      exit 1

let () = main Sys.argv