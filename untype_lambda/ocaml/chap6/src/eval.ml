
type bool =
| True
| False

type nat =
| O
| S of nat

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n m =
  match n with
  | O -> (match m with
          | O -> True
          | S _ -> False)
  | S n' -> (match m with
             | O -> False
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> True
  | S n' -> (match m with
             | O -> False
             | S m' -> leb n' m')

type term =
| Var of nat
| Abs of term
| App of term * term

(** val shift : nat -> nat -> term -> term **)

let rec shift d c = function
| Var k -> (match leb c k with
            | True -> (match d with
                       | O -> Var (sub k (S O))
                       | S _ -> Var (add k d))
            | False -> Var k)
| Abs t1 -> Abs (shift d (add c (S O)) t1)
| App (t1, t2) -> App ((shift d c t1), (shift d c t2))

(** val up : nat -> term -> term **)

let up n t =
  shift n O t

(** val subst : nat -> term -> term -> term **)

let rec subst j s = function
| Var k -> (match eqb j k with
            | True -> s
            | False -> Var k)
| Abs t1 -> Abs (subst (add j (S O)) (up (S O) s) t1)
| App (t1, t2) -> App ((subst j s t1), (subst j s t2))

(** val vb : term -> bool **)

let vb = function
| Abs _ -> True
| _ -> False

type optiont =
| Some of term
| None

(** val step : term -> optiont **)

let rec step = function
| App (t1, t2) ->
  (match t1 with
   | Abs t3 ->
     (match vb t2 with
      | True -> Some (up O (subst O (up (S O) t2) t3))
      | False -> (match step t2 with
                  | Some t2' -> Some (App (t1, t2'))
                  | None -> None))
   | _ -> (match step t1 with
           | Some t1' -> Some (App (t1', t2))
           | None -> None))
| _ -> None
