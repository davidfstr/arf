open Core.Std

type
  program = {
    (* Main function is the first function in the list *)
    funcs : func list
  } and
  
  func = {
    name : string;
    param_var : string;
    body : stmt list
  } and
  
  stmt =
    | AssignLiteral of stmt_AssignLiteral
    | AssignCall of stmt_AssignCall
    | If of stmt_If
    | Return of stmt_Return
    and
  stmt_AssignLiteral = {
    target_var : string;
    literal : simple_typ
  } and
  stmt_AssignCall = {
    target_var : string;
    func_name : string;
    arg_var : string
  } and
  stmt_If = {
    then_block : stmt list;
    else_block : stmt list
  } and
  stmt_Return = {
    result_var : string
  } and
  
  simple_typ =
    | NoneType
    | Bool
    | Int
  
  with sexp
