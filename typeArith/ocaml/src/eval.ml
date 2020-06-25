
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

(** val natValue : term -> bool **)

let rec natValue = function
| O -> True
| Succ t1 -> natValue t1
| _ -> False

(** val value : term -> bool **)

let rec value t0 = match t0 with
| Tru -> True
| Fls -> True
| _ -> natValue t0

type t =
| Bool
| Nat

type optionT =
| SomeT of t
| NoneT

(** val eqT : t -> t -> bool **)

let eqT t1 t2 =
  match t1 with
  | Bool -> (match t2 with
             | Bool -> True
             | Nat -> False)
  | Nat -> (match t2 with
            | Bool -> False
            | Nat -> True)

(** val has_type : term -> optionT **)

let rec has_type = function
| If (t1, t2, t3) ->
  (match has_type t1 with
   | SomeT t4 ->
     (match t4 with
      | Bool ->
        (match has_type t2 with
         | SomeT t5 ->
           (match has_type t3 with
            | SomeT t6 -> (match eqT t5 t6 with
                           | True -> SomeT t5
                           | False -> NoneT)
            | NoneT -> NoneT)
         | NoneT -> NoneT)
      | Nat -> NoneT)
   | NoneT -> NoneT)
| O -> SomeT Nat
| Succ t1 -> (match has_type t1 with
              | SomeT t2 -> (match t2 with
                             | Bool -> NoneT
                             | Nat -> SomeT Nat)
              | NoneT -> NoneT)
| Pred t1 -> (match has_type t1 with
              | SomeT t2 -> (match t2 with
                             | Bool -> NoneT
                             | Nat -> SomeT Nat)
              | NoneT -> NoneT)
| Iszero t1 ->
  (match has_type t1 with
   | SomeT t2 -> (match t2 with
                  | Bool -> NoneT
                  | Nat -> SomeT Bool)
   | NoneT -> NoneT)
| _ -> SomeT Bool

type optiont =
| Some of term
| None

(** val eval : term -> optiont **)

let rec eval = function
| If (t1, t2, t3) ->
  (match value t1 with
   | True -> (match t1 with
              | Tru -> Some t2
              | Fls -> Some t3
              | _ -> None)
   | False -> (match eval t1 with
               | Some t1' -> Some (If (t1', t2, t3))
               | None -> None))
| Succ t1 ->
  (match natValue t1 with
   | True -> None
   | False -> (match eval t1 with
               | Some t1' -> Some (Succ t1')
               | None -> None))
| Pred t1 ->
  (match natValue t1 with
   | True -> (match t1 with
              | O -> Some O
              | Succ nv1 -> Some nv1
              | _ -> None)
   | False -> (match eval t1 with
               | Some t1' -> Some (Pred t1')
               | None -> None))
| Iszero t1 ->
  (match natValue t1 with
   | True -> (match t1 with
              | O -> Some Tru
              | Succ _ -> Some Fls
              | _ -> None)
   | False -> (match eval t1 with
               | Some t1' -> Some (Iszero t1')
               | None -> None))
| _ -> None
