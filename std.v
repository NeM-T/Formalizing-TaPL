From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Notation eqb_eq_str := String.eqb_eq.
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

Fixpoint my_nth {A: Type} n (l: list A) :=
  match n with
  | 0 =>
    match l with
    | [] => None
    | a :: ctx' => Some a
    end
  | S n' =>
    match l with
    | [] => None
    | x :: ctx' => my_nth n' ctx'
    end
  end.

Lemma len_eq_none : forall A (ctx: list A),
    my_nth (length ctx) ctx = None.
Proof.
  induction ctx; auto.
Qed.

Lemma leb_len_none : forall A n (ctx: list A),
    (Nat.leb (length ctx) n) = true ->
    my_nth n ctx = None.
Proof.
  induction n; intros; auto.
  destruct ctx; auto. simpl in H. inversion H.
  destruct ctx. simpl. reflexivity.
  simpl. apply IHn. apply Nat.leb_le. apply le_S_n. apply Nat.leb_le. apply H.
Qed.

Lemma app_getbind : forall A (ctx ctx': list A) n,
    my_nth (n + (length ctx)) (ctx ++ ctx') = my_nth n ctx'.
Proof.
  induction ctx; simpl; intros; auto.
  rewrite <- plus_n_O; reflexivity.
  rewrite <- plus_Snm_nSm. simpl. apply IHctx.
Qed.

Lemma lt_len_Someapp : forall A n (ctx ctx1 ctx2: list A) T,
    n < length ctx ->
    my_nth n (ctx ++ ctx1) = Some T ->
    my_nth n (ctx ++ ctx2) = Some T.
Proof.
  induction n; simpl; intros. destruct ctx. inversion H. simpl. simpl in H0. apply H0.
  destruct ctx. inversion H. simpl. destruct ( (a :: ctx) ++ ctx1) eqn:IHH. inversion H0. inversion IHH; subst.
  eapply IHn in H0. apply H0. simpl in H. apply lt_S_n in H. apply H.
Qed.

Lemma len_app_a : forall A (ctx ctx': list A) a,
    my_nth (length ctx) (ctx ++ a :: ctx') = Some a.
Proof.
  induction ctx; auto.
Qed.
