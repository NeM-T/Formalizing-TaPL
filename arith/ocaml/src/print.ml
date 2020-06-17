open Eval

let rec eval_string t =
  match t with
  | Tru -> "Tru"
  | Fls -> "Fls"
  | If (t1, t2, t3) -> "If " ^ (eval_string t1) ^ " THEN " ^ (eval_string t2) ^ " ELSE " ^ (eval_string t3)
  | O   -> "0"
  | Succ t1 -> "S (" ^ (eval_string t1) ^ ")"
  | Pred t1 -> "Pred " ^ (eval_string t1)
  | Iszero t1 -> "Is0 " ^ (eval_string t1)


let rec manyeval t1 =
  match eval1 t1 with
  | Some t1' -> manyeval t1'
  | _        -> t1

