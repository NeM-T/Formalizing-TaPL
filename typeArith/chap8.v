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

Lemma valueNB : forall t,
    Vb t = true -> t \in Nat \/ t \in Bool.
Proof.
  induction t; intros; try solve_by_invert.
  right. apply T_True. right. apply T_False.
  left. apply T_Zero. inversion H. left.
  apply T_Succ. apply Vb_correct in H. apply NatValueType. apply NVb_correct; auto.
Qed.

Lemma multieval_trance :forall t1 t2 t3,
    t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros. generalize dependent t3. induction H; intros; auto.
  eapply multi_step. apply H. auto.
Qed.

Lemma if_trance : forall t t' t2 t3,
    t -->* t' -> If t t2 t3 -->* If t' t2 t3.
Proof.
  intros. induction H.
  apply multi_refl. eapply multi_step. apply E_If. apply H. apply IHmulti.
Qed.

Lemma value_nostep : forall t,
    value t -> eval t = None.
Proof.
  intros. destruct t; try solve_by_inverts 2; try reflexivity; simpl.
  inversion H. apply NVb_correct in H0. inversion H0. rewrite H3. reflexivity.
Qed.

Lemma NVb_Vb_false : forall t,
    Vb t = false -> NVb t = false.
Proof.
  induction t; intros; try solve_by_invert; auto.
Qed.

Theorem stopeval : forall t,
    exists t', eval t' = None /\ t -->* t'.
Proof with eauto.
  induction t.
  -
    exists Tru; split... apply multi_refl.
  -
    exists Fls; split; auto; apply multi_refl.
  -
    inversion IHt1. inversion IHt2. inversion IHt3. clear IHt3. clear IHt2. clear IHt1.
    destruct H. destruct H0. destruct H1.
    destruct (Vb x) eqn:IH1.
    generalize IH1. apply valueNB in IH1. inversion IH1; intros.
    exists (If x t2 t3).
    destruct x; try solve_by_invert; split; try reflexivity; simpl.
    apply if_trance. apply H2.
    inversion IH0. rewrite H7. reflexivity.
    apply if_trance...

    destruct x; try solve_by_invert.
    exists x0. split; auto.
    apply multieval_trance with (t2:= (If Tru t2 t3)).
    apply if_trance... eapply multi_step. apply E_IfTrue. auto.

    exists x1; split; auto.
    apply multieval_trance with (t2:= (If Fls t2 t3)).
    apply if_trance... eapply multi_step. apply E_IfFalse. auto.

    exists (If x t2 t3). split; simpl. rewrite IH1. rewrite H; reflexivity.
    apply if_trance...
  -
    exists O; split; auto. apply multi_refl.
  -
    inversion IHt. destruct H. exists (succ x); split; simpl.
    destruct (NVb x)... rewrite H. reflexivity.
    generalize H0; clear; intros.
    induction H0. apply multi_refl. eapply multi_step. apply E_Succ... apply IHmulti.
  -
    inversion IHt. clear IHt. destruct H.
    destruct (Vb x) eqn:IH1. generalize IH1; intros. apply valueNB in IH1. inversion IH1.
    destruct x; try solve_by_invert.
    exists O. split... apply multieval_trance with (pred O). generalize H0; clear; intros. induction H0.
    apply multi_refl. eapply multi_step. apply E_Pred. apply H. apply IHmulti.
    eapply multi_step. apply E_PredZero. apply multi_refl.

    exists x. split; simpl.
    inversion IH0. apply NVb_correct in H3. apply v_nat in H3. apply value_nostep in H3. apply H3.
    apply multieval_trance with (pred (succ x)). generalize H0. clear; intros. induction H0.
    apply multi_refl. eapply multi_step. apply E_Pred. apply H. apply IHmulti.
    eapply multi_step. apply E_PredSucc. inversion IH0. apply NVb_correct... apply multi_refl.

    destruct x; try solve_by_invert.
    exists (pred Tru). split...
    generalize H0; clear; intros; induction H0.
    apply multi_refl. eapply multi_step. apply E_Pred... apply IHmulti.

    exists (pred Fls). split...
    generalize H0; clear; intros; induction H0.
    apply multi_refl. eapply multi_step. apply E_Pred... apply IHmulti.

    exists (pred x). simpl; split. apply NVb_Vb_false in IH1. rewrite IH1. rewrite H. reflexivity.
    generalize H0; clear; intros; induction H0. apply multi_refl.
    eapply multi_step... apply E_Pred...

  -
    inversion IHt. clear IHt. destruct H.
    destruct (NVb x) eqn:IH1.
    destruct x; try solve_by_invert.
    exists Tru. split... apply multieval_trance with (iszero O).
    generalize H0; clear; intros; induction H0. apply multi_refl. eapply multi_step. apply E_IsZero...
    apply IHmulti. eapply multi_step. apply E_IsZeroZero. apply multi_refl.

    exists (Fls). split... apply multieval_trance with (iszero (succ x)).
    generalize H0; clear; intros; induction H0. apply multi_refl. eapply multi_step. apply E_IsZero...
    apply IHmulti. eapply multi_step. apply E_IsZeroSucc. inversion IH1. apply NVb_correct... apply multi_refl.

    exists (iszero x). split; simpl. rewrite IH1. rewrite H. reflexivity.
    generalize H0; clear; intros; induction H0. apply multi_refl. eapply multi_step. apply E_IsZero... apply IHmulti.
Qed.
