
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val add : nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type context = char list list

type term =
| Var of nat * nat
| Abs of char list * term
| App of term * term

(** val ctxlen : context -> nat **)

let ctxlen =
  length

(** val eqb_string : char list -> char list -> bool **)

let eqb_string =
  eqb

(** val in0 : char list -> context -> bool **)

let rec in0 name = function
| [] -> false
| n1::m -> if eqb_string name n1 then true else in0 name m

(** val newname : context -> char list -> nat -> char list **)

let rec newname ctx name n0 =
  if in0 name ctx
  then (match n0 with
        | O -> append name ('1'::('0'::[]))
        | S n' -> newname ctx (append name ('\''::[])) n')
  else name

(** val pickfreshname :
    context -> char list -> (char list list, char list) prod **)

let pickfreshname ctx name =
  let name' = newname ctx name (S (S (S (S (S (S (S (S (S (S O)))))))))) in
  Pair ((name'::ctx), name')

(** val eqb_nat : nat -> nat -> bool **)

let rec eqb_nat n1 n2 =
  match n1 with
  | O -> (match n2 with
          | O -> true
          | S _ -> false)
  | S n1' -> (match n2 with
              | O -> false
              | S n2' -> eqb_nat n1' n2')

(** val leb : nat -> nat -> bool **)

let rec leb n1 n2 =
  if eqb_nat n1 n2
  then true
  else (match n2 with
        | O -> false
        | S n2' -> leb n1 n2')

(** val index2name : nat -> context -> char list option **)

let rec index2name n0 ctx =
  match n0 with
  | O -> (match ctx with
          | [] -> None
          | x::_ -> Some x)
  | S n' -> (match ctx with
             | [] -> None
             | _::ctx' -> index2name n' ctx')

type n =
| P of nat
| M1

(** val shift_walk : nat -> n -> term -> term **)

let rec shift_walk c d = function
| Var (x, n0) ->
  if leb c x
  then (match d with
        | P d' -> Var ((add x d'), (add n0 d'))
        | M1 -> Var ((sub x (S O)), (sub n0 (S O))))
  else (match d with
        | P d' -> Var (x, (add n0 d'))
        | M1 -> Var (x, (sub n0 (S O))))
| Abs (x, t1) -> Abs (x, (shift_walk (S c) d t1))
| App (t1, t2) -> App ((shift_walk c d t1), (shift_walk c d t2))

(** val shift : n -> term -> term **)

let shift d t =
  shift_walk O d t

(** val sub_walk : nat -> term -> n -> term -> term **)

let rec sub_walk j s c = function
| Var (x, n0) ->
  let jc = match c with
           | P c' -> add j c'
           | M1 -> sub j (S O) in
  if eqb_nat x jc then shift c s else Var (x, n0)
| Abs (x, t1) ->
  let sc = match c with
           | P c' -> P (add c' (S O))
           | M1 -> P O in
  Abs (x, (sub_walk j s sc t1))
| App (t1, t2) -> App ((sub_walk j s c t1), (sub_walk j s c t2))

(** val sub0 : nat -> term -> term -> term **)

let sub0 j s t =
  sub_walk j s (P O) t

(** val subtop : term -> term -> term **)

let subtop s t =
  shift M1 (sub0 O (shift (P (S O)) s) t)

(** val isval : term -> bool **)

let isval = function
| Abs (_, _) -> true
| _ -> false

(** val eval : term -> term option **)

let rec eval = function
| App (t1, t2) ->
  (match t1 with
   | Abs (_, t12) ->
     if isval t2
     then Some (subtop t2 t12)
     else (match eval t2 with
           | Some t2' -> Some (App (t1, t2'))
           | None -> None)
   | _ -> (match eval t1 with
           | Some t1' -> Some (App (t1', t2))
           | None -> None))
| _ -> None

(** val printtm : context -> term -> char list **)

let rec printtm ctx = function
| Var (x, n0) ->
  if eqb_nat (ctxlen ctx) n0
  then (match index2name x ctx with
        | Some str -> str
        | None -> 'N'::('o'::('n'::('e'::[]))))
  else '['::('B'::('a'::('d'::('I'::('n'::('d'::('e'::('x'::(']'::[])))))))))
| Abs (x, t1) ->
  let Pair (ctx', x') = pickfreshname ctx x in
  append
    (append
      (append (append ('('::('\206'::('\187'::[]))) x') ('.'::(' '::[])))
      (printtm ctx' t1)) (')'::[])
| App (t1, t2) ->
  append
    (append (append (append ('('::[]) (printtm ctx t1)) (' '::[]))
      (printtm ctx t2)) (')'::[])

(** val test_eval : term -> char list **)

let test_eval t =
  match eval t with
  | Some t' -> printtm [] t'
  | None -> 'N'::('o'::('t'::('E'::('v'::('a'::('l'::[]))))))
