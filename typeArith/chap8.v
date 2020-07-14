Require Coq.extraction.Extraction.
Extraction Language OCaml.
Add LoadPath "../arith/".
Require Import chap3.
Import ArithNat.

Inductive T : Type :=
| Bool
| Nat.

Inductive hastype : term -> T -> Prop :=
| T_True : hastype Tru Bool
| T_False: hastype Fls Bool
| T_If :
    forall (t1 t2 t3: term)(T': T),
      hastype t1 Bool ->
      hastype t2 T' -> hastype t3 T' ->
      hastype (If t1 t2 t3) T'
| T_Zero : hastype O Nat
| T_Succ :
    forall (t1: term),
      hastype t1 Nat ->
      hastype (succ t1) Nat
| T_Pred :
    forall (t1: term),
      hastype t1 Nat ->
      hastype (pred t1) Nat
| T_IsZero :
    forall (t1: term),
      hastype t1 Nat ->
      hastype (iszero t1) Bool.
Notation "t '\in' T" := (hastype t T)(at level 40).


Inductive optionT : Type :=
| SomeT (T1: T)
| NoneT.

Definition eqT (T1 T2: T) : bool :=
  match (T1, T2) with
  | (Bool, Bool) => true
  | (Nat,  Nat)  => true
  | _ => false
  end.

Fixpoint has_type (t: term) : optionT :=
  match t with
  | Tru => SomeT Bool
  | Fls => SomeT Bool
  | If t1 t2 t3 =>
    match has_type t1 with
    | SomeT Bool =>
      match has_type t2 with
      | SomeT T1 =>
        match has_type t3 with
        | SomeT T2 => if (eqT T1 T2) then SomeT T1 else NoneT
        | _ => NoneT
        end
      | _ => NoneT
      end
    | _ => NoneT
    end
  | O => SomeT Nat
  | succ t1 =>
    match has_type t1 with
    | SomeT Nat => SomeT Nat
    | _ => NoneT
    end
  | pred t1 =>
    match has_type t1 with
    | SomeT Nat => SomeT Nat
    | _ => NoneT
    end
  | iszero t1 =>
    match has_type t1 with
    | SomeT Nat => SomeT Bool
    | _ => NoneT
    end
  end.

Lemma eqT2Prop : forall T1 T2,
    eqT T1 T2 = true <-> T1 = T2.
Proof.
  intros. split;
  destruct T1; destruct T2; intros; auto; discriminate.
Qed.

Lemma has_typeCorrect : forall t T1,
    t \in T1 <-> has_type t = SomeT T1.
Proof.
  split.
  -
    generalize dependent T1. induction t; intros; inversion H; subst; auto; simpl.
    +
      apply IHt1 in H3. apply IHt2 in H5. apply IHt3 in H6.
      rewrite H3. rewrite H5. rewrite H6. destruct T1; auto.
    +
      apply IHt in H1. rewrite H1; auto.
    +
      apply IHt in H1. rewrite H1; auto.
    +
      apply IHt in H1. rewrite H1; auto.
  -
    generalize dependent T1. induction t; intros; inversion H; subst; auto.
    +
      apply T_True.
    +
      apply T_False.
    +
      destruct (has_type t1); try (discriminate). destruct (T0); try discriminate.
      destruct (has_type t2) eqn:Ht2; try (discriminate). destruct (has_type t3) eqn:Ht3; try discriminate.
      destruct (eqT T2 T3) eqn:eq; try discriminate. apply T_If.
      apply IHt1; auto. apply IHt2; auto. apply eqT2Prop in eq. apply IHt3; rewrite <- eq; auto.
    +
      apply T_Zero.
    +
      destruct (has_type t). destruct T0. inversion H1. inversion H1. apply T_Succ. apply IHt; auto. inversion H1.
    +
      destruct (has_type t). destruct T0. inversion H1. inversion H1. apply T_Pred. apply IHt; auto. inversion H1.
    +
      destruct (has_type t). destruct T0. inversion H1. inversion H1. apply T_IsZero. apply IHt; auto. inversion H1.
Qed.


Lemma l8_2_2_1 : forall R,
    Tru \in R -> R = Bool.
Proof. intros. inversion H; auto. Qed.

Lemma l8_2_2_3 : forall t1 t2 t3 R,
    If t1 t2 t3 \in R -> t1 \in Bool /\ t2 \in R /\ t3 \in R.
Proof. intros. inversion H; subst. split; auto. Qed.

Theorem t8_2_4 : forall t R1 R2,
    t \in R1 -> t \in R2 -> R1 = R2.
Proof. intros. induction H; inversion H0; auto. Qed.

Lemma l8_3_1_1 : forall v ,
    value v -> v \in Bool -> v = Tru \/ v = Fls.
Proof. intros. inversion H0; subst; auto; inversion H. inversion H4. inversion H2. Qed.

Lemma l8_3_1_2 : forall v,
    value v -> v \in Nat -> NatValue v .
Proof.
  intros. inversion H0; subst; auto.
  inversion H. inversion H4.
  apply nv_O. inversion H. inversion H2; subst. apply nv_S; auto.
  inversion H. inversion H2.
Qed.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step: term -> term -> Prop :=
| E_IfTrue : forall t2 t3,
    If Tru t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If Fls t2 t3 --> t3
| E_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3
| E_Succ : forall t1 t1',
    t1 --> t1' -> succ t1 --> succ t1'
| E_PredZero :
    pred O --> O
| E_PredSucc : forall nv1,
    NatValue nv1 -> pred (succ nv1) --> nv1
| E_Pred : forall t1 t1',
    t1 --> t1' -> pred t1 --> pred t1'
| E_IsZeroZero :
    iszero O --> Tru
| E_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) --> Fls
| E_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

  where " t '-->' t' " := (step t t').

Inductive optiont : Type :=
| Some (T: term)
| None.

Fixpoint NVb (t: term) : bool :=
  match t with
  | O => true
  | succ t1 => NVb t1
  | _ => false
  end.

Definition Vb (t: term) : bool :=
  match t with
  | Tru => true
  | Fls => true
  | _ => NVb t
  end.

Fixpoint eval (t: term) : optiont :=
  match t with
  | If t1 t2 t3 =>
    if (Vb t1) then
      match t1 with
      | Tru => Some t2
      | Fls => Some t3
      | _ => None
      end else
      match (eval t1) with
      | Some t1' => Some (If t1' t2 t3)
      | _ => None
      end
  | succ t1 =>
    if NVb t1 then
      None else
      match (eval t1) with
      | Some t1' => Some (succ t1')
      | _ => None
      end
  | pred t1 =>
    if (NVb t1) then
      match t1 with
      | O => Some O
      | succ nv1 => Some nv1
      | _ => None
      end else
      match (eval t1) with
      | Some t1' => Some (pred t1')
      | _ => None
      end
  | iszero t1 =>
    if (NVb t1) then
      match t1 with
      | O => Some Tru
      | succ _ => Some Fls
      | _ => None
      end else
      match (eval t1) with
      | Some t1' => Some (iszero t1')
      | _ => None
      end
  | _ => None
  end.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.


Lemma Valuestop : forall t1,
    Vb t1 = true -> not (exists t1', t1 --> t1').
Proof.
  induction t1; intros; intro H1; try solve_by_inverts 2.
  inversion H.
  assert (Vb t1 = true). destruct t1; try solve_by_invert; auto.
  apply IHt1 in H0. inversion H1. inversion H3; subst. induction H0. exists t1'; auto.
Qed.


Lemma NVb_correct : forall t,
    NatValue t <-> NVb t = true.
Proof.
  split; intros.
  -
    induction H; auto.
  -
    induction t; try solve_by_invert; auto.
    apply nv_O. inversion H. apply nv_S; auto.
Qed.

Theorem step_eval1_correct : forall t1 t1',
    eval t1 = Some t1' <-> t1 --> t1'.
Proof.
  split.
  -
    intros. generalize dependent t1'.
    induction t1; intros; try solve_by_invert.
    +
      inversion H. destruct (Vb t1_1). destruct (t1_1); try solve_by_invert.
      inversion H. apply E_IfTrue. inversion H. apply E_IfFalse.
      destruct (eval t1_1); try solve_by_invert. inversion H1. apply E_If. apply IHt1_1; auto.
    +
      inversion H. destruct (NVb t1). inversion H1. destruct (eval t1). inversion H1. apply E_Succ. apply IHt1; auto. inversion H1.
    +
      inversion H. destruct (NVb t1) eqn:nv. destruct (t1); try (solve_by_invert). inversion H1. apply E_PredZero.
      inversion H1. apply E_PredSucc. inversion nv. rewrite <- H2. apply NVb_correct; auto.
      destruct (eval t1). inversion H1. apply E_Pred. apply IHt1; auto.
      inversion H1.
    +
      inversion H. destruct (NVb t1) eqn:nv. destruct t1; try solve_by_invert.
      inversion H1. apply E_IsZeroZero. inversion H1. apply E_IsZeroSucc. inversion nv. apply NVb_correct; auto.
      destruct (eval t1). inversion H1. apply E_IsZero. apply IHt1; auto. inversion H1.

  -
    generalize dependent t1'; induction t1; intros; try (solve_by_invert).
    +
      inversion H; subst; auto.
      simpl. destruct (Vb t1_1) eqn:Ht1. induction Valuestop with(t1:= t1_1); auto. eauto.
      apply IHt1_1 in H4. rewrite H4; auto.
    +
      simpl. inversion H; subst. destruct (NVb t1) eqn:nv.
      induction (Valuestop t1). destruct (t1); try solve_by_invert; auto. eauto.
      apply IHt1 in H1. rewrite H1; auto.
    +
      inversion H; subst; auto. simpl. apply NVb_correct in H1. rewrite H1; auto.
      simpl. destruct (NVb t1) eqn:nv. induction (Valuestop t1). destruct t1; try solve_by_invert.
      simpl. inversion nv; auto. eauto.
      apply IHt1 in H1. rewrite H1; auto.
    +
      inversion H; subst; auto. simpl. apply NVb_correct in H1. rewrite H1; auto.
      simpl. destruct (NVb t1) eqn:nv. induction (Valuestop t1). destruct t1; try solve_by_invert; eauto. eauto.
      apply IHt1 in H1. rewrite H1; auto.
Qed.

Extraction "ocaml/src/eval.ml" eval has_type.

Lemma Vb_correct : forall t,
    value t <-> Vb t = true.
Proof with eauto.
  split; intros.
  -
    induction H; auto. inversion H. auto. simpl. apply NVb_correct; auto.
  -
    induction t; try solve_by_invert; auto. apply v_tru. apply v_fls.
    apply v_nat. apply nv_O. apply v_nat. inversion H. apply nv_S; apply NVb_correct; auto.
Qed.

Theorem l8_3_2 : forall t T',
    t \in T' -> Vb t = true \/ exists t', t --> t'.
Proof with eauto.
  induction t; intros; auto.
  - (*If*)
    inversion H. inversion H0; subst. generalize H3. right. apply IHt1 in H3.
    inversion H3. apply l8_3_1_1 in H0; auto. inversion H0; subst. exists t2. apply E_IfTrue. exists t3; apply E_IfFalse. apply Vb_correct; auto.
    inversion H1. exists (If x t2 t3). apply E_If; auto.
  - (*Succ*)
    inversion H; subst. generalize H1. apply IHt in H1. inversion H1. left. apply l8_3_1_2 in H2; auto. simpl. apply NVb_correct; auto. apply Vb_correct...
    inversion H0. right. exists (succ x). apply E_Succ...
  - (*Pred*)
    inversion H; subst. generalize H1. right. apply IHt in H1. inversion H1. apply Vb_correct in H2. apply l8_3_1_2 in H2...
    destruct t; inversion H2. exists O. apply E_PredZero. exists t. apply E_PredSucc... inversion H2. exists (pred x). apply E_Pred...
  - (*iszero*)
    inversion H; subst. generalize H1. right. apply IHt in H1. inversion H1.
    apply l8_3_1_2 in H0... destruct t; inversion H0. exists Tru. apply E_IsZeroZero. exists Fls. apply E_IsZeroSucc... apply Vb_correct...
    inversion H2. exists (iszero x). apply E_IsZero...
Qed.

Theorem l8_3_3: forall t t' T,
    t \in T /\ t --> t' -> t' \in T.
Proof.
  induction t; intros; inversion H. inversion H1. inversion H1.
  -
    inversion H0; inversion H1; subst; auto. apply T_If; auto.
  -
    inversion H1.
  -
    inversion H1; inversion H0; subst. apply T_Succ. apply IHt. split; auto.
  -
    inversion H1; inversion H0; subst. apply T_Zero. inversion H6; auto. apply T_Pred. apply IHt. split; auto.
  -
    inversion H0; inversion H1; subst. apply T_True. apply T_False. apply T_IsZero. apply IHt. split; auto.
Qed.

Theorem l8_3_6: forall t' T, exists t,
    t --> t' -> t' \in T -> not (t \in T).
Proof.
  exists (If Tru Tru O). intros.
  intro HH. inversion HH; subst. inversion H6; inversion H7; subst. inversion H3.
Qed.

Reserved Notation " t '==>' t' " (at level 40).

Inductive bigstep : term -> term -> Prop :=
| B_Value : forall t1,
    value t1 -> t1 ==> t1
| B_IfTrue : forall t1 t2 v2 t3,
    t1 ==> Tru -> t2 ==> v2 -> value v2 -> If t1 t2 t3 ==> v2
| B_IfFalse : forall t1 t2 t3 v3,
    t1 ==> Fls -> t3 ==> v3 -> value v3 -> If t1 t2 t3 ==> v3
| B_Succ : forall t1 nv1,
    t1 ==> nv1 -> NatValue nv1 -> succ t1 ==> succ nv1
| B_PredZero : forall t1,
    t1 ==> O -> pred t1 ==> O
| B_PredSucc : forall t1 nv1,
    t1 ==> (succ nv1) -> NatValue nv1 -> pred t1 ==> nv1
| B_IsZeroZero : forall t1,
    t1 ==> O -> iszero t1 ==> Tru
| B_IsZeroSucc : forall t1 nv1,
    t1 ==> (succ nv1) -> NatValue nv1 -> iszero t1 ==> Fls

  where " t '==>' t' " := (bigstep t t').

Lemma NatValueType : forall t1,
    NatValue t1 -> t1 \in Nat.
Proof. intros. induction t1; inversion H. apply T_Zero. apply T_Succ. apply IHt1. auto. Qed.

Lemma l8_3_7_preservation : forall t t' T,
    t \in T /\ t ==> t' -> t' \in T.
Proof with eauto.
  induction t; intros; inversion H. inversion H1; subst... inversion H1; subst...
  -
    inversion H1; inversion H0; subst. inversion H2. inversion H3. apply IHt2... apply IHt3...
  -
    inversion H1...
  -
    inversion H1; subst... inversion H0; subst. apply T_Succ. apply IHt...
  -
    inversion H0; inversion H1; subst. inversion H5. inversion H2. apply T_Zero. apply NatValueType...
  -
    inversion H0; inversion H1; subst... apply T_True. apply T_False.
Qed.

Lemma l8_3_7_progress : forall t T',
    t \in T' -> (exists t', t ==> t' /\ Vb t' = true).
Proof with eauto.
  induction t; intros.
  -
    exists Tru; split... apply B_Value... apply v_tru.
  -
    exists Fls; split... apply B_Value... apply v_fls.
  -
    inversion H; subst. generalize H3. intros. apply IHt1 in H3. inversion H3. inversion H1.
    assert (x \in Bool). eapply l8_3_7_preservation. split. apply H0. apply H2.
    apply l8_3_1_1 in H7... inversion H7.
    apply IHt2 in H5. inversion H5. inversion H9. exists x0. subst. split. apply B_IfTrue... apply Vb_correct; auto. apply H11.
    apply IHt3 in H6; inversion H6. inversion H9. exists x0; subst. split... apply B_IfFalse... apply Vb_correct; apply H11. apply Vb_correct; apply H4.
  -
    exists O. split... apply B_Value... apply v_nat. apply nv_O.
  -
    inversion H;subst. generalize H1. apply IHt in H1. inversion H1. inversion H0. exists (succ x).
    apply Vb_correct in H3. apply l8_3_1_2 in H3; auto.
    split. apply B_Succ... simpl. apply NVb_correct; auto.
    apply l8_3_7_preservation with (t:= t). split...
  -
    inversion H; subst. generalize H1. apply IHt in H1. inversion H1. inversion H0. intro.
    apply Vb_correct in H3. apply l8_3_1_2 in H3. destruct x; inversion H3. exists O. split. apply B_PredZero... auto.
    exists x. split... apply B_PredSucc... apply Vb_correct. apply v_nat; auto. 
    apply l8_3_7_preservation with (t:= t)...
  -
    inversion H; subst. generalize H1. apply IHt in H1. inversion H1. inversion H0. intro.
    apply Vb_correct in H3. apply l8_3_1_2 in H3. destruct x; inversion H3. exists Tru. split... apply B_IsZeroZero...
    exists Fls. split... apply B_IsZeroSucc with (nv1:= x)... apply l8_3_7_preservation with (t:= t)...
Qed.

Definition stop (t1: term) :=
  Vb t1 = false  /\ not (exists t1', t1 --> t1').

Theorem has_typeStop: forall t,
    stop t -> has_type t = NoneT.
Proof with eauto.
  induction t; intros; destruct H; try solve_by_invert.
  -
    simpl. destruct (has_type t1) eqn:Tt1... destruct T1... destruct (has_type t2) eqn:Tt2... destruct (has_type t3) eqn:Tt3... destruct (eqT T1 T0) eqn:eq...
    induction H0.
    assert (If t1 t2 t3 \in T1).
    apply has_typeCorrect. simpl. rewrite Tt1. rewrite Tt2. rewrite Tt3. rewrite eq...
    apply l8_3_2 in H0. inversion H0. inversion H1. auto.
  -
    simpl. destruct (has_type t) eqn:Ht... destruct T1... induction H0.
    assert (succ t \in Nat). apply has_typeCorrect. simpl. rewrite Ht...
    apply l8_3_2 in H0. inversion H0. rewrite H1 in H. discriminate. auto.
  -
    simpl. destruct (has_type t) eqn:Ht... destruct T1... induction H0.
    assert (pred t \in Nat). apply has_typeCorrect. simpl. rewrite Ht...
    apply l8_3_2 in H0. inversion H0. discriminate. auto.
  -
    simpl. destruct (has_type t) eqn:Ht... destruct T1... induction H0.
    assert (iszero t \in Bool). apply has_typeCorrect. simpl. rewrite Ht...
    apply l8_3_2 in H0. inversion H0. discriminate. auto.
Qed.
