
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val length : 'a1 list -> nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : char list -> char list -> bool

val append : char list -> char list -> char list

type context = char list list

type term =
| Var of nat * nat
| Abs of char list * term
| App of term * term

val ctxlen : context -> nat

val eqb_string : char list -> char list -> bool

val in0 : char list -> context -> bool

val newname : context -> char list -> nat -> char list

val pickfreshname : context -> char list -> (char list list, char list) prod

val eqb_nat : nat -> nat -> bool

val leb : nat -> nat -> bool

val index2name : nat -> context -> char list option

type n =
| P of nat
| M1

val shift_walk : nat -> n -> term -> term

val shift : n -> term -> term

val sub_walk : nat -> term -> n -> term -> term

val sub0 : nat -> term -> term -> term

val subtop : term -> term -> term

val isval : term -> bool

val eval : term -> term option

val printtm : context -> term -> char list

val test_eval : term -> char list
