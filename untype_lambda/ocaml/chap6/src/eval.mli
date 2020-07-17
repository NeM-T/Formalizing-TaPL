
type bool =
| True
| False

type nat =
| O
| S of nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : nat -> nat -> bool

val leb : nat -> nat -> bool

type term =
| Var of nat
| Abs of term
| App of term * term

val shift : nat -> nat -> term -> term

val up : nat -> term -> term

val subst : nat -> term -> term -> term

val vb : term -> bool

type optiont =
| Some of term
| None

val step : term -> optiont
