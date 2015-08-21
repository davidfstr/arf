open Core.Std

type
  program = {
    (* Main function is the first function in the list *)
    funcs : func list
  } and
  
  func = {
    name : string;
    param : string;
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
    literal : typ
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
  
  typ =
    | NoneType
    | Bool
    | Int

let input = {
  funcs = [
    {
      name = "main";
      param = "x";
      body = [
        Return {
          result_var = "x"
        }
      ]
    }
  ]
}

let () = printf "Hello\n"
