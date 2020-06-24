
Definition tru {A:Type} {B:Type} : A -> B -> A :=
  fun t => fun f => t.

Definition fls {A:Type} {B:Type} : A -> B -> B :=
  fun t => fun f => f.

Notation test := (fun l => fun m => fun n => l m n).

Goal forall (A B: Type) (a:A) (b: B), test tru a b = a.
Proof. reflexivity. Qed.

Notation And :=
  (fun b => fun c => b c fls).

Notation Or :=
  (fun b => fun c => b tru c).

Compute (And tru fls).

Compute (Or fls tru).

Notation no :=
  (fun b => (b fls tru)).

Inductive church : Type :=
| Z
| S (z1: church).

Compute ((fun s => fun z => z) S Z ).


From Coq Require Import Strings.String.


Inductive term : Type :=
  | var : string -> term
  | abs : string -> term -> term
  | app : term -> term -> term.


Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

(*
       [x:=s]x = s
       [x:=s]y = y if x <> y
       [x:=s](\x:T11. t12) = \x:T11. t12
       [x:=s](\y:T11. t12) = \y:T11. [x:=s]t12 if x <> y
       [x:=s](t1 t2) = ([x:=s]t1) ([x:=s]t2)
*)

Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' t1 =>
      abs x'  (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive value : term -> Prop :=
  | v_abs : forall x t,
      value (abs x t).

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive eval : term -> term -> Prop :=
  | E_AppAbs : forall x t12 v2,
         value v2 ->
         (app (abs x t12) v2) --> [x:=v2]t12
  | E_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | E_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1 t2'
where "t1 '-->' t2" := (eval t1 t2).

Hint Constructors eval.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    multi R y z ->
                    multi R x z.

Notation multieval := (multi eval).
Notation "t1 '-->*' t2" := (multieval t1 t2) (at level 40).

Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.
