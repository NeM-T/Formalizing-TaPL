
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

type string =
| EmptyString
| String of char * string

val eqb : string -> string -> bool

val append : string -> string -> string

type context = string list

type term =
| Var of nat * nat
| Abs of string * term
| App of term * term

val ctxlen : context -> nat

val eqb_string : string -> string -> bool

val in0 : string -> context -> bool

val newname : context -> string -> nat -> string

val pickfreshname : context -> string -> (string list, string) prod

val eqb_nat : nat -> nat -> bool

val leb : nat -> nat -> bool

val index2name : nat -> context -> string option

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

val printtm : context -> term -> string

val test_eval : term -> string
