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
  token = {
    content : token_content;
    indent : int
  } and
  
  token_content =
    | TDef of token_TDef
    | TAssignLiteral of token_TAssignLiteral
    | TAssignCall of token_TAssignCall
    | TReturn of token_TReturn
    | TIf
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
      let indent = (String.length line_with_indent) - (String.length line) in
      
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
          let ok token_content =
            Ok { content = token_content; indent = indent } in
          
          let error message =
            Error (ParseError message) in
          
          if Str.string_match t_def_re line 0 then
            let name = Str.matched_group 1 line in
            let param_var = Str.matched_group 2 line in
            ok (TDef { name; param_var })
          
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
                ok (TAssignLiteral { target_var; literal_type })
              
              | None ->
                (* TODO: Emit parse error: unrecognized literal type *)
                error ("unrecognized literal type: " ^ literal_type_iden)
            )
          
          else if Str.string_match t_assign_call_re line 0 then
            let target_var = Str.matched_group 1 line in
            let func_name = Str.matched_group 2 line in
            let arg_var = Str.matched_group 3 line in
            ok (TAssignCall { target_var; func_name; arg_var })
          
          else if Str.string_match t_return_re line 0 then
            let result_var = Str.matched_group 1 line in
            ok (TReturn { result_var })
          
          else if line = "if:" then
            ok TIf
            
          else if line = "else:" then
            ok TElse
          
          else if line = "pass" then
            ok TPass
            
          else
            (* TODO: Emit parse error: unrecognized statement *)
            error ("line syntax not understood: " ^ line)
          in
        
        let open Result.Monad_infix in
        token_result >>= fun token ->
        tokenize next_lines >>= fun next_tokens ->
        Ok (token :: next_tokens)

(* -------------------------------------------------------------------------- *)
(* Parser *)

type indent_constraint =
  (* Just entering a new statement block *)
  | IndentRightOf of int
  (* Continuing within an existing statement block *)
  | IndentAt of int

let rec (parse_stmt_list :
    token list -> indent_constraint -> ((stmt list * token list), parse_error) Result.t)
    tokens indent_constraint =
  match tokens with
    | [] ->
      (match indent_constraint with
        | IndentRightOf _ ->
          Error (ParseError "expected statement list but found EOF")
        
        | IndentAt _ ->
          Ok ([], [])
      )
  
    | (token :: next_tokens) ->
      (* NOTE: Captures: token, next_tokens *)
      let finish_with_end_of_list () =
        Ok ([], token :: next_tokens) in
      
      let finish_with_error message =
        Error (ParseError message) in
      
      let continue_with_ok_indent () =
        (* NOTE: Captures: token *)
        let parse_stmt_list_tail next_tokens =
          parse_stmt_list next_tokens (IndentAt token.indent) in
        
        let continue_with_stmt stmt next_tokens =
          let open Result.Monad_infix in
          parse_stmt_list_tail next_tokens >>= fun (next_stmts, next_tokens) ->
          Ok (stmt :: next_stmts, next_tokens)
          in
        
        (* NOTE: Captures: next_tokens *)
        let continue_with_simple_stmt stmt =
          continue_with_stmt stmt next_tokens in
        
        (* NOTE: Captures: next_tokens *)
        let continue_after_skipped_stmt () =
          parse_stmt_list_tail next_tokens in
        
        match token.content with
          | TDef _ ->
            finish_with_error ("encountered top-level statement inside block: " ^ (token_to_string token))
          
          | TAssignLiteral { target_var; literal_type } ->
            continue_with_simple_stmt (AssignLiteral { target_var; literal_type })
            
          | TAssignCall { target_var; func_name; arg_var } ->
            continue_with_simple_stmt (AssignCall { target_var; func_name; arg_var })
            
          | TReturn { result_var } ->
            continue_with_simple_stmt (Return { result_var })
          
          | TIf ->
            let parse_else next_tokens =
              match next_tokens with
                | [] ->
                  finish_with_error "expected 'else' but found EOF"
                
                | ({ content = TElse; indent = else_indent } :: next_tokens) ->
                  if else_indent = token.indent then
                    Ok next_tokens
                  else
                    finish_with_error "expected 'else' to be indented to same level as paired 'if'"
                
                | (other_token :: next_tokens) ->
                  finish_with_error ("expected 'else' but found: " ^ (token_to_string other_token))
              in
            
            let open Result.Monad_infix in
            parse_stmt_list next_tokens (IndentRightOf token.indent)
              >>= fun (then_block, next_tokens) ->
            parse_else next_tokens
              >>= fun next_tokens ->
            parse_stmt_list next_tokens (IndentRightOf token.indent)
              >>= fun (else_block, next_tokens) ->
            continue_with_stmt (If { then_block; else_block }) next_tokens
          
          | TElse ->
            finish_with_error "orphaned 'else' clause"
          
          | TPass ->
            continue_after_skipped_stmt ()
          
        in
      
      (* Check indentation *)
      match indent_constraint with
        | IndentRightOf minlim_indent ->
          if token.indent <= minlim_indent then
            finish_with_error ("unexpected unindent: " ^ (token_to_string token))
          else
            continue_with_ok_indent ()
        
        | IndentAt block_indent ->
          if token.indent > block_indent then
            finish_with_error ("unexpected indent: " ^ (token_to_string token))
          else if token.indent < block_indent then
            finish_with_end_of_list ()
          else
            continue_with_ok_indent ()

let rec (parse_func_list : token list -> (func list, parse_error) Result.t) tokens =
  match tokens with
    | [] ->
      Ok []
    
    | { content = TDef { name; param_var }; indent = indent } :: next_tokens ->
      let open Result.Monad_infix in
      parse_stmt_list next_tokens (IndentRightOf indent) >>= fun (body, next_tokens) ->
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
  (* TODO: Improve output format. Match the README *)
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