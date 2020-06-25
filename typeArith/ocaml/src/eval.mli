
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

val natValue : term -> bool

val value : term -> bool

type t =
| Bool
| Nat

type optionT =
| SomeT of t
| NoneT

val eqT : t -> t -> bool

val has_type : term -> optionT

type optiont =
| Some of term
| None

val eval : term -> optiont
