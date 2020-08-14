From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v) (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).


Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.


Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros. reflexivity. Qed.


Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite eqb_refl. reflexivity.
Qed.


Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
 unfold t_update. intros. apply eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold t_update.  extensionality y. induction (String.eqb x y). reflexivity. reflexivity.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (String.eqb x y).
Proof.
  intros. destruct String.eqb eqn:H.
 - apply eqb_eq in H. apply ReflectT. apply H.
 - apply eqb_neq in H. apply ReflectF. apply H.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update. extensionality y.
  destruct String.eqb eqn:H.
  -  apply eqb_eq in H. rewrite H. reflexivity.
  - reflexivity.
Qed.


Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. unfold t_update. extensionality y.
   destruct (String.eqb x1 y) eqn:H1.
 - apply eqb_eq in H1. rewrite H1 in H. apply eqb_neq in H. rewrite H. reflexivity.
 - reflexivity.
Qed.


(*Partial maps*)
Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v :A) := (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Fixpoint eqb_nat (n1 n2: nat) :=
  match n1 with
  | 0 =>
    match n2 with
    | 0 => true
    | _ => false
    end
  | S n1' =>
    match n2 with
    | 0 => false
    | S n2' => eqb_nat n1' n2'
    end
  end.

Fixpoint leb (n1 n2: nat) :=
  if eqb_nat n1 n2 then true else
    match n2 with
    | 0 => false
    | S n2' => leb n1 n2'
    end.



Lemma eqb_eq : forall n1 n2,
    eqb_nat n1 n2 = true <-> eq n1 n2.
Proof.
  split. generalize dependent n2.
  induction n1; induction n2; intros; auto. inversion H. inversion H.

  generalize dependent n2; induction n1; induction n2; intros; auto; simpl.
  inversion H. inversion H. apply IHn1. inversion H. auto.
Qed.

Lemma leb_le : forall n1 n2,
    n1 <= n2 -> leb n1 n2 = true.
Proof.
  intros. induction H; simpl.
  -
    induction n1; auto. simpl.
    assert (eqb_nat n1 n1 = true). apply eqb_eq. auto.
    rewrite H. reflexivity.
  -
    destruct (eqb_nat n1 (S m)); auto.
Qed.

Lemma le_trance : forall n1 n2 n3,
    n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  intros. generalize dependent n3. induction H; intros; auto.
  destruct H0. apply IHle. apply le_S. apply le_n.
  apply IHle. apply le_S. apply le_S_n. apply le_S. apply H0.
Qed.


Lemma le_leb : forall n1 n2,
    leb n1 n2 = true -> n1 <= n2.
Proof.
  destruct n1; intros.
  apply le_0_n.
  induction n2. inversion H. inversion H.
  destruct (eqb_nat n1 n2) eqn: IH1. apply eqb_eq in IH1. rewrite IH1; auto.
  apply IHn2 in H1. apply le_S. apply H1.
Qed.

Lemma le_eq_leb : forall n1 n2,
    leb n1 n2 = true <-> n1 <= n2.
Proof.
  split. apply le_leb. apply leb_le.
Qed.

Lemma leb0 : forall n,
    leb 0 n = true.
Proof.
  induction n; auto.
Qed.

Lemma leb_F : forall n1 n2,
    leb n1 n2 = false <-> not (le n1 n2).
Proof.
  split; intros. intro. apply leb_le in H0. rewrite H in H0; inversion H0.
  destruct n1. induction H. apply Nat.le_0_l. generalize dependent n1; induction n2; intros.
  reflexivity. simpl. destruct eqb_nat eqn:IH. apply eqb_eq in IH; subst. induction H. apply Nat.le_refl.
  apply IHn2. intro. apply H. apply le_leb. simpl. rewrite IH. apply leb_le. apply H0.
Qed.

Lemma leb_neq : forall n1 n2,
    leb n1 n2 = false -> n2 < n1.
Proof.
  intros. apply leb_F in H. apply Nat.nle_gt in H. auto.
Qed.

Lemma eqb_refl : forall n,
    eqb_nat n n = true.
Proof.
  induction n; auto.
Qed.


Lemma leb_refl : forall n,
    leb n n = true.
Proof.
  induction n; auto. simpl. rewrite eqb_refl. reflexivity.
Qed.

Definition ltb n1 n2 :=
  leb (S n1) n2.

Lemma ltb_lt : forall n1 n2,
    ltb n1 n2 = true <-> lt n1 n2.
Proof.
  unfold lt, ltb; split; intros; apply le_eq_leb; auto.
Qed.

Lemma lt_0_s_f : forall n,
    ltb 0 (S n) = true.
Proof.
  induction n; auto.
Qed.

Lemma ltb_neq : forall n1 n2,
    ltb n1 n2 = false <-> not (n1 < n2).
Proof.
  unfold ltb, lt. intros. apply leb_F.
Qed.
