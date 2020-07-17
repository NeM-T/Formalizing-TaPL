open Eval

let rec nat2int n = 
  match n with
  | O    -> 0
  | S n' -> 1 + (nat2int n')

let rec eval_string t =
  match t with
  | App (t1, t2) -> "App ( " ^ (eval_string t1) ^ " ) ( " ^ (eval_string t2) ^ " )"
  | Abs t1       -> "Abs ( " ^ (eval_string t1) ^ " )"
  | Var n        -> string_of_int (nat2int n)

let eval t =
  match step t with
  | Some t' -> t'
  | None    -> t
