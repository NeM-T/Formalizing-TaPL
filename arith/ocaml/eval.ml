
type bool =
| True
| False

type term =
| Tru
| Fls
| If of term * term * term
| O
| Succ of term
| Pred of term
| Iszero of term

(** val isnumericval : term -> bool **)

let rec isnumericval = function
| O -> True
| Succ t1 -> isnumericval t1
| _ -> False

(** val isval : term -> bool **)

let rec isval t = match t with
| Tru -> True
| Fls -> True
| _ -> isnumericval t

type optiont =
| Some of term
| None

(** val eval1 : term -> optiont **)

let rec eval1 = function
| If (t1, t2, t3) ->
  (match isval t1 with
   | True -> (match t1 with
              | Tru -> Some t2
              | Fls -> Some t3
              | _ -> None)
   | False -> (match eval1 t1 with
               | Some t1' -> Some (If (t1', t2, t3))
               | None -> None))
| Succ t1 ->
  (match isnumericval t1 with
   | True -> None
   | False -> (match eval1 t1 with
               | Some t1' -> Some (Succ t1')
               | None -> None))
| Pred t1 ->
  (match isnumericval t1 with
   | True -> (match t1 with
              | O -> Some O
              | Succ nv1 -> Some nv1
              | _ -> None)
   | False -> (match eval1 t1 with
               | Some t1' -> Some (Pred t1')
               | None -> None))
| Iszero t1 ->
  (match isnumericval t1 with
   | True -> (match t1 with
              | O -> Some Tru
              | Succ _ -> Some Fls
              | _ -> None)
   | False -> (match eval1 t1 with
               | Some t1' -> Some (Iszero t1')
               | None -> None))
| _ -> None
