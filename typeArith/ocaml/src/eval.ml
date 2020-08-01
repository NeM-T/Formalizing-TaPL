
type bool =
| True
| False

module ArithNat =
 struct
  type term =
  | Tru
  | Fls
  | If of term * term * term
  | O
  | Coq_succ of term
  | Coq_pred of term
  | Coq_iszero of term
 end

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

(** val has_type : ArithNat.term -> optionT **)

let rec has_type = function
| ArithNat.If (t1, t2, t3) ->
  (match has_type t1 with
   | SomeT t4 ->
     (match t4 with
      | Bool ->
        (match has_type t2 with
         | SomeT t5 ->
           (match has_type t3 with
            | SomeT t6 ->
              (match eqT t5 t6 with
               | True -> SomeT t5
               | False -> NoneT)
            | NoneT -> NoneT)
         | NoneT -> NoneT)
      | Nat -> NoneT)
   | NoneT -> NoneT)
| ArithNat.O -> SomeT Nat
| ArithNat.Coq_succ t1 ->
  (match has_type t1 with
   | SomeT t2 ->
     (match t2 with
      | Bool -> NoneT
      | Nat -> SomeT Nat)
   | NoneT -> NoneT)
| ArithNat.Coq_pred t1 ->
  (match has_type t1 with
   | SomeT t2 ->
     (match t2 with
      | Bool -> NoneT
      | Nat -> SomeT Nat)
   | NoneT -> NoneT)
| ArithNat.Coq_iszero t1 ->
  (match has_type t1 with
   | SomeT t2 ->
     (match t2 with
      | Bool -> NoneT
      | Nat -> SomeT Bool)
   | NoneT -> NoneT)
| _ -> SomeT Bool

type optiont =
| Some of ArithNat.term
| None

(** val nVb : ArithNat.term -> bool **)

let rec nVb = function
| ArithNat.O -> True
| ArithNat.Coq_succ t1 -> nVb t1
| _ -> False

(** val vb : ArithNat.term -> bool **)

let vb t0 = match t0 with
| ArithNat.Tru -> True
| ArithNat.Fls -> True
| _ -> nVb t0

(** val eval : ArithNat.term -> optiont **)

let rec eval = function
| ArithNat.If (t1, t2, t3) ->
  (match vb t1 with
   | True ->
     (match t1 with
      | ArithNat.Tru -> Some t2
      | ArithNat.Fls -> Some t3
      | _ -> None)
   | False ->
     (match eval t1 with
      | Some t1' -> Some (ArithNat.If (t1', t2, t3))
      | None -> None))
| ArithNat.Coq_succ t1 ->
  (match nVb t1 with
   | True -> None
   | False ->
     (match eval t1 with
      | Some t1' -> Some (ArithNat.Coq_succ t1')
      | None -> None))
| ArithNat.Coq_pred t1 ->
  (match nVb t1 with
   | True ->
     (match t1 with
      | ArithNat.O -> Some ArithNat.O
      | ArithNat.Coq_succ nv1 -> Some nv1
      | _ -> None)
   | False ->
     (match eval t1 with
      | Some t1' -> Some (ArithNat.Coq_pred t1')
      | None -> None))
| ArithNat.Coq_iszero t1 ->
  (match nVb t1 with
   | True ->
     (match t1 with
      | ArithNat.O -> Some ArithNat.Tru
      | ArithNat.Coq_succ _ -> Some ArithNat.Fls
      | _ -> None)
   | False ->
     (match eval t1 with
      | Some t1' -> Some (ArithNat.Coq_iszero t1')
      | None -> None))
| _ -> None
