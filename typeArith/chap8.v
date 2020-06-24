Inductive term : Type :=
| Tru
| Fls
| If (t1 t2 t3: term)
| O
| Succ (t1: term)
| Pred (t1: term)
| iszero (t1: term).

Fixpoint NatValue (t: term) : bool :=
  match t with
  | O => true
  | Succ t1 => NatValue t1
  | _ => false
  end.

Fixpoint Value (t: term) : bool :=
  match t with
  | Tru => true
  | Fls => true
  | _ => NatValue t
  end.

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
      hastype (Succ t1) Nat
| T_Pred :
    forall (t1: term),
      hastype t1 Nat ->
      hastype (Pred t1) Nat
| T_IsZero :
    forall (t1: term),
      hastype t1 Nat ->
      hastype (iszero t1) Bool.

Notation "t '\in' T" := (hastype t T)(at level 40).

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
    Value v = true -> v \in Bool -> v = Tru \/ v = Fls.
Proof. intros. inversion H0; subst; auto; inversion H. Qed.

Lemma l8_3_1_2 : forall v,
    Value v = true -> v \in Nat -> NatValue v = true.
Proof. intros. inversion H0; subst; auto. Qed.

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
    t1 --> t1' -> Succ t1 --> Succ t1'
| E_PredZero :
    Pred O --> O
| E_PredSucc : forall nv1,
    NatValue nv1 = true -> Pred (Succ nv1) --> nv1
| E_Pred : forall t1 t1',
    t1 --> t1' -> Pred t1 --> Pred t1'
| E_IsZeroZero :
    iszero O --> Tru
| E_IsZeroSucc : forall nv1,
    NatValue nv1 = true -> iszero (Succ nv1) --> Fls
| E_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

  where " t '-->' t' " := (step t t').


Theorem l8_3_2 : forall t T',
    t \in T' -> Value t = true \/ exists t', t --> t'.
Proof with eauto.
  induction t; intros; auto.
  - (*If*)
    inversion H. inversion H0; subst. generalize H3. right. apply IHt1 in H3.
    inversion H3. apply l8_3_1_1 in H0; auto. inversion H0; subst. exists t2. apply E_IfTrue. exists t3; apply E_IfFalse.
    inversion H1. exists (If x t2 t3). apply E_If; auto.
  - (*Succ*)
    inversion H; subst. generalize H1. apply IHt in H1. inversion H1. left. apply l8_3_1_2 in H2; auto.
    inversion H0. right. exists (Succ x). apply E_Succ...
  - (*Pred*)
    inversion H; subst. generalize H1. right. apply IHt in H1. inversion H1. apply l8_3_1_2 in H2...
    destruct t; inversion H2. exists O. apply E_PredZero. exists t. apply E_PredSucc... inversion H2. exists (Pred x). apply E_Pred...
  - (*iszero*)
    inversion H; subst. generalize H1. right. apply IHt in H1. inversion H1.
    apply l8_3_1_2 in H0... destruct t; inversion H0. exists Tru. apply E_IsZeroZero. exists Fls. apply E_IsZeroSucc...
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
    Value t1 = true -> t1 ==> t1
| B_IfTrue : forall t1 t2 v2 t3,
    t1 ==> Tru -> t2 ==> v2 -> Value v2 = true -> If t1 t2 t3 ==> v2
| B_IfFalse : forall t1 t2 t3 v3,
    t1 ==> Fls -> t3 ==> v3 -> Value v3 = true -> If t1 t2 t3 ==> v3
| B_Succ : forall t1 nv1,
    t1 ==> nv1 -> NatValue nv1 = true -> Succ t1 ==> Succ nv1
| B_PredZero : forall t1,
    t1 ==> O -> Pred t1 ==> O
| B_PredSucc : forall t1 nv1,
    t1 ==> (Succ nv1) -> NatValue nv1 = true -> Pred t1 ==> nv1
| B_IsZeroZero : forall t1,
    t1 ==> O -> iszero t1 ==> Tru
| B_IsZeroSucc : forall t1 nv1,
    t1 ==> (Succ nv1) -> NatValue nv1 = true -> iszero t1 ==> Fls

  where " t '==>' t' " := (bigstep t t').

Lemma NatValueType : forall t1,
    NatValue t1 = true -> t1 \in Nat.
Proof. intros. induction t1; inversion H. apply T_Zero. apply T_Succ. apply IHt1. auto. Qed.

Lemma l8_3_7_preservation : forall t t' T,
    t \in T /\ t ==> t' -> t' \in T.
Proof with eauto.
  induction t; intros; inversion H. inversion H1; subst... inversion H1; subst...
  -
    inversion H1; inversion H0; subst. inversion H2. apply IHt2... apply IHt3...
  -
    inversion H1...
  -
    inversion H1; subst... inversion H0; subst. apply T_Succ. apply IHt...
  -
    inversion H0; inversion H1; subst. inversion H5. apply T_Zero. apply NatValueType...
  -
    inversion H0; inversion H1; subst... apply T_True. apply T_False.
Qed.

Lemma l8_3_7_progress : forall t T',
    t \in T' -> (exists t', t ==> t' /\ Value t' = true).
Proof with eauto.
  induction t; intros.
  -
    exists Tru; split... apply B_Value...
  -
    exists Fls; split... apply B_Value...
  -
    inversion H; subst. generalize H3. intros. apply IHt1 in H3. inversion H3. inversion H1.
    assert (x \in Bool). eapply l8_3_7_preservation. split. apply H0. apply H2.
    apply l8_3_1_1 in H7... inversion H7.
    apply IHt2 in H5. inversion H5. inversion H9. exists x0. subst. split. apply B_IfTrue... apply H11.
    apply IHt3 in H6; inversion H6. inversion H9. exists x0; subst. split... apply B_IfFalse...
  -
    exists O. split... apply B_Value...
  -
    inversion H;subst. generalize H1. apply IHt in H1. inversion H1. inversion H0. exists (Succ x).
    apply l8_3_1_2 in H3; auto.
    split. apply B_Succ... auto. apply l8_3_7_preservation with (t:= t). split...
  -
    inversion H; subst. generalize H1. apply IHt in H1. inversion H1. inversion H0. intro.
    apply l8_3_1_2 in H3. destruct x; inversion H3. exists O. split. apply B_PredZero... auto.
    exists x. split... apply B_PredSucc... generalize H6. clear. induction x; intros H; inversion H...
    apply l8_3_7_preservation with (t:= t)...
  -
    inversion H; subst. generalize H1. apply IHt in H1. inversion H1. inversion H0. intro.
    apply l8_3_1_2 in H3. destruct x; inversion H3. exists Tru. split... apply B_IsZeroZero...
    exists Fls. split... apply B_IsZeroSucc with (nv1:= x)... apply l8_3_7_preservation with (t:= t)...
Qed.
