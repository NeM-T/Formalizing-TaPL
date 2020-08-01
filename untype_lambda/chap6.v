Require Coq.extraction.Extraction.
Extraction Language OCaml.

Inductive term : Type :=
| Var : nat -> term
| Abs : term -> term
| App : term -> term -> term.

Notation beta_ShiftNum := 0.

Fixpoint shift (d c: nat) (t: term) : term :=
  match t with
  | Var k =>
    if Nat.leb c k then
      match d with
      | beta_ShiftNum => Var (k - 1)
      | _ => Var (k + d)
      end
    else Var k
  | Abs t1 => Abs (shift d (c + 1) t1)
  | App t1 t2 => App (shift d c t1) (shift d c t2)
  end.

Definition up (n: nat) (t: term) : term := shift n 0 t.

Compute ( up 2 (Abs (Abs (App (Var 1) (App (Var 0) (Var 2) ))))). (* = Abs (Abs (App (Var 1) (App (Var 0) (Var 4)))) *)
Compute ( up 2 (Abs (App (Var 0) (App (Var 1)(Abs (App (Var 0)(App (Var 1)(Var 2)))))))). (* = Abs (App (Var 0) (App (Var 3) (Abs (App (Var 0) (App (Var 1) (Var 4)))))) *)

Fixpoint subst (j: nat) (s t: term) : term :=
  match t with
  | Var k =>
    if Nat.eqb j k then s else Var k
  | Abs t1 =>
    Abs (subst (j + 1) (up 1 s) t1)
  | App t1 t2 =>
    App (subst j s t1) (subst j s t2)
  end.

Compute (subst 0 (Var 1) (App (Var 0) (Abs(Abs (Var 2))))).  (* = App (Var 1) (Abs (Abs (Var 3))) *)
Compute (subst 0 (App (Var 1) (Abs (Var 2))) (App (Var 0) (Abs (Var 1)))). (* = App (App (Var 1) (Abs (Var 2))) (Abs (App (Var 2) (Abs (Var 3)))) *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive value : term -> Prop :=
  | v_abs : forall n,
      value (Abs n).

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive eval : term -> term -> Prop :=
  | E_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      App t1 t2 --> App t1' t2
  | E_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      App v1 t2 --> App v1 t2'
  | E_AppAbs : forall t1 v2,
      value v2 ->
      App (Abs t1) v2 -->
          up beta_ShiftNum ([0 := up 1 (v2)] t1)

  where " t '-->' t' " := (eval t t').

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multieval := (multi eval).
Notation "t1 '-->*' t2" := (multieval t1 t2) (at level 40).

Definition vb (t: term) :=
  match t with
  | Abs _ => true
  | _ => false
  end.

Lemma vbValue : forall t,
    vb t = true <-> value t.
Proof.
  destruct t; split; intros; inversion H; auto.
  apply v_abs.
Qed.

Inductive optiont : Type :=
| Some (t: term)
| None.

Fixpoint step (t: term) : optiont :=
  match t with
  | App t1 t2 =>
    match t1 with
    | Abs t3 =>
      if vb t2 then
        Some (up beta_ShiftNum ([0 := up 1 (t2)] t3)) else
        match step t2 with
        | Some t2' => Some (App t1 t2')
        | None => None
        end
    | _ =>
      match step t1 with
      | Some t1' =>
        Some (App t1' t2)
      | None => None
      end
    end
  | _ => None
  end.
Extraction "ocaml/chap6/src/eval.ml" step.

Lemma stepeval : forall t t',
    t --> t' <-> step t = Some t'.
Proof.
  split; intros.
  -
    induction H.
    +
      simpl. destruct t1. inversion H. inversion H.
      rewrite IHeval. reflexivity.
    +
      simpl. inversion H; subst. destruct t2. inversion H0. inversion H0. rewrite IHeval. simpl. reflexivity.
    +
      inversion H; subst. simpl. reflexivity.
  -
    generalize dependent t'.
    induction t; intros. inversion H. inversion H.
    simpl in H.
    destruct t1. inversion H. destruct (vb t2) eqn:IH2. inversion H. apply E_AppAbs. apply vbValue; auto.
    destruct (step t2) eqn:IHH. inversion H.
    apply E_App2. apply v_abs. apply IHt2. reflexivity.
    inversion H.
    destruct (step (App t1_1 t1_2)). inversion H. apply E_App1. apply IHt1. reflexivity.
    inversion H.
Qed.


(*評価の一意性*)
Lemma determine : forall t t' t'',
    t --> t' -> t --> t'' -> t' = t''.
Proof.
  intros; generalize dependent t''. induction H; intros.
  -
    inversion H0; subst.
    apply IHeval in H4. rewrite H4; reflexivity.
    inversion H3; subst. inversion H.
    inversion H.
  -
    inversion H1; subst. inversion H; subst; inversion H5.
    apply IHeval in H6. rewrite H6; reflexivity.
    inversion H5; subst; inversion H0.
  -
    inversion H; inversion H0; subst.
    inversion H5. inversion H6.
    reflexivity.
Qed.

Fixpoint size (t: term) : nat :=
  match t with
  | Var _ => 1
  | Abs t1 => 1 + (size t1)
  | App t1 t2 => (size t1) + (size t2)
  end.

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

Lemma eqb_eq : forall n1 n2,
    eqb_nat n1 n2 = true <-> eq n1 n2.
Proof.
  split. generalize dependent n2.
  induction n1; induction n2; intros; auto. inversion H. inversion H.

  generalize dependent n2; induction n1; induction n2; intros; auto; simpl.
  inversion H. inversion H. apply IHn1. inversion H. auto.
Qed.

Fixpoint leb (n1 n2: nat) :=
  if eqb_nat n1 n2 then true else
    match n2 with
    | 0 => false
    | S n2' => leb n1 n2'
    end.

Fixpoint fv_card (t: term) (n: nat) :=
  match t with
  | Var n1 =>
    if leb n n1 then 1 else 0
  | Abs t1 =>
    fv_card (t1) (n + 1)
  | App t1 t2 =>
    (fv_card t1 n) + (fv_card t2 n)
  end.

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

Lemma le_leb : forall n1 n2,
    leb n1 n2 = true -> n1 <= n2.
Proof.
  destruct n1; intros.
  apply le_0_n.
  induction n2. inversion H. inversion H.
  destruct (eqb_nat n1 n2) eqn: IH1. apply eqb_eq in IH1. rewrite IH1; auto.
  apply IHn2 in H1. apply le_S. apply H1.
Qed.

Lemma le_trance : forall n1 n2 n3,
    n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  intros. generalize dependent n3. induction H; intros; auto.
  destruct H0. apply IHle. apply le_S. apply le_n.
  apply IHle. apply le_S. apply le_S_n. apply le_S. apply H0.
Qed.

From Coq Require Import Strings.String.

Lemma fv_le : forall t n,
  fv_card t (n + 1) <= fv_card t n.
Proof.
  induction t; intros; simpl; auto.
  destruct (leb n0 n) eqn:IH1; destruct (leb (n0 + 1) n) eqn:IH2; auto.
  apply le_leb in IH2. rewrite PeanoNat.Nat.add_1_r in IH2. apply Le.le_Sn_le in IH2. apply leb_le in IH2. rewrite IH1 in IH2. inversion IH2.
  apply PeanoNat.Nat.add_le_mono; auto.
Qed.

Lemma e5_3_3 : forall t,
    fv_card t 0 <= (size (t)).
Proof.
  induction t; simpl; auto.
  -
    destruct (leb 0 n); auto.
  -
    apply le_trance with (fv_card t 0); auto. apply (fv_le t 0).
  -
    apply PeanoNat.Nat.add_le_mono; auto.
Qed.
