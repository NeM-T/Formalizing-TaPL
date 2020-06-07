
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

val isnumericval : term -> bool

val isval : term -> bool

type optiont =
| Some of term
| None

val eval1 : term -> optiont
