
type bool =
| True
| False

module ArithNat :
 sig
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

val eqT : t -> t -> bool

val has_type : ArithNat.term -> optionT

type optiont =
| Some of ArithNat.term
| None

val nVb : ArithNat.term -> bool

val vb : ArithNat.term -> bool

val eval : ArithNat.term -> optiont
