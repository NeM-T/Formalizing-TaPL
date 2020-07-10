
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
From Coq Require Import List.
Import List.ListNotations.

Inductive term : Type :=
  | var : string -> term
  | abs : string -> term -> term
  | app : term -> term -> term.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Fixpoint In (a:string) (l:list string) : bool :=
  match l with
    | [] => false
    | b :: m => if eqb_string b a then true else In a m
  end.

Fixpoint FV (t : term) (l: list string) : (list string) :=
  match t with
  | var x => if In x l then [] else [x]
  | abs x t1 => FV t1 (x :: l)
  | app t1 t2 => (FV t1 l) ++ (FV t2 (l ++ (FV t1 l)))
  end.

Fixpoint size (t: term) : nat :=
  match t with
  | var _ => 1
  | abs _ t1 => 1 + (size t1)
  | app t1 t2 => (size t1) + (size t2)
  end.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

Lemma le_FV : forall t l,
    length (FV t l) <= length((FV t nil)).
Proof.
  induction t; intros; simpl.
  -
    destruct (In s l); auto.
  -
    admit.
  -
    rewrite app_length. rewrite app_length. apply PeanoNat.Nat.add_le_mono; auto.
    clear IHt1.
Abort.

Lemma e5_3_3 : forall t,
    le (length (FV t nil)) (size (t)).
Proof.
  induction t; simpl; auto.
  -
    apply PeanoNat.Nat.le_trans with(m:= length(FV t [])); auto.
    admit.
  -
    rewrite app_length. apply PeanoNat.Nat.add_le_mono; auto.
    apply PeanoNat.Nat.le_trans with(m:= length(FV t2 [])); auto.
Abort.

Fixpoint FV2 (t : term) (l: list string) : (list string) :=
  match t with
  | var s => if In s l then nil else [s]
  | abs s t1 => FV2 t1 (s :: l)
  | app t1 t2 => (FV2 t1 l) ++ (FV2 t2 l)
  end.


Lemma e5_3_3 : forall t,
    le (length (FV2 t nil)) (size (t)).
Proof.
  induction t; simpl; auto.
  -
    apply PeanoNat.Nat.le_trans with(m:= length(FV2 t [])); auto.
    clear.
    induction t; simpl; auto.
    +
      destruct (eqb_string s s0); auto.
    +
      admit.
    +
      rewrite app_length. rewrite app_length.
      apply PeanoNat.Nat.add_le_mono; auto.
  -
    rewrite app_length. apply PeanoNat.Nat.add_le_mono; auto.
Abort.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : term) (t : term) : option term :=
  match t with
  | var x' =>
      if eqb_string x x' then Some s else Some t
  | abs y t1 =>
    if eqb_string x y then Some (abs y t1) else
      if In y (FV s []) then None else
        match [x:= s] t1 with
        |Some t' => Some (abs y t')
        | None => None
        end
  | app t1 t2 =>
    match [x:= s] t1 with
    | Some t1' =>
      match ([x:=s] t2) with
      | Some t2' => Some (app t1' t2')
      | None => None
      end
    | None => None
    end
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Compute (["x":= (app (var "y")(var "z"))] (abs "w" (app (var "x") (var "w")))).

Inductive value : term -> Prop :=
  | v_abs : forall x t,
      value (abs x t).

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive eval : term -> term -> Prop :=
  | E_AppAbs : forall x t12 v2 t',
         value v2 ->
         [x:= v2]t12 = Some t' ->
         (app (abs x t12) v2) --> t'
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

Lemma determin  : forall t t' t'',
    t --> t' -> t --> t'' -> t' = t''.
Proof.
  intros. generalize dependent t''. induction H; intros.
  -
    inversion H1; subst .
    rewrite H0 in H7. inversion H7; auto.
    inversion H5. inversion H; subst. inversion H6.
  -
    inversion H0; subst. inversion H.
    apply IHeval in H4. rewrite H4; auto. inversion H3; subst. inversion H.
  -
    inversion H1; subst. inversion H4; subst. inversion H0.
    inversion H; subst. inversion H5.
    apply IHeval in H6. rewrite H6; auto.
Qed.

Close Scope string_scope.
