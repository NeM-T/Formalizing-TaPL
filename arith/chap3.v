
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.



Module ArithC.

Inductive t : Type :=
| true
| false
| If (t1 t2 t3: t)
| O (*オーです*)
| succ (t1: t)
| pred (t1: t)
| iszero (t1: t).

Fixpoint Const_num (T: t) : nat :=
  match T with
  | true => 1
  | false => 1
  | O => 1
  | succ t1 => Const_num t1
  | pred t1 => Const_num t1
  | iszero t1 => Const_num t1
  | If t1 t2 t3 => (Const_num t1) + (Const_num t2) + (Const_num t3)
  end.

Fixpoint size (T: t) : nat :=
  match T with
  | true => 1
  | false => 1
  | O => 1
  | succ t1 => 1 + (size t1)
  | pred t1 => 1 + (size t1)
  | iszero t1 => 1 + (size t1)
  | If t1 t2 t3 => 1 +  (size t1) + (size t2) + (size t3)
  end.

Lemma l3_3: forall T,
    Const_num T <= size T.
Proof.
  induction T; auto.
  - (*If*)
    simpl. induction IHT1. induction IHT2. induction IHT3; auto.
    rewrite plus_n_Sm in IHIHT3; apply le_S; assumption.
    apply le_S. rewrite <- plus_n_Sm. rewrite plus_Sn_m. assumption.
    apply le_S; assumption.
  - (*succ*)
    simpl. inversion IHT; auto.
  - (*pred*)
    simpl. inversion IHT; auto.
  - (*iszero*)
    simpl. inversion IHT; auto.
Qed.

Fixpoint depth (T: t): nat :=
  match T with
  | true => 1
  | false => 1
  | O => 1
  | succ t1 => 1 + depth t1
  | pred t1 => 1 + depth t1
  | iszero t1 => 1 + depth t1
  | If t1 t2 t3 => (Nat.max (depth t1) (Nat.max (depth t2) (depth t3) ))
  end.

End ArithC.

Module ArithBool.

Inductive t : Type :=
| true
| false
| If (t1 t2 t3: t).

Inductive value : t -> Prop :=
| v_true : value true
| v_false: value false.


Reserved Notation " t '-->' t' " (at level 40).

Inductive step : t -> t -> Prop :=
| E_IfTrue : forall t2 t3,
    If true t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If false t2 t3 --> t3
| E_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3

  where " t '-->' t' " := (step t t').


Theorem T3_5_4 : forall t t' t'', (*決定性*)
    t --> t' -> t --> t'' -> t' = t''.
Proof.
  intros. generalize dependent t''.
  induction H; intros.
  - (*E_Iftrue*)
    inversion H0; subst; auto. inversion H4.
  - (*E_IfFalse*)
    inversion H0; subst; auto. inversion H4.
  - (*E_If*)
    inversion H0; subst. inversion H. inversion H.
    apply IHstep in H5; subst; auto.
Qed.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma L_origin : forall t t' t'',
    t -->* t' -> t' -->* t'' -> t -->* t''.
Proof.
  intros. generalize dependent t''. induction H; intros; try assumption.
  eapply multi_step. apply H. apply IHmulti in H1. assumption.
Qed.


Theorem T3_5_11 : forall t u u',
    t -->* u -> t -->* u' -> value u -> value u' -> u = u'.
Proof.
  intros. generalize dependent u'. induction H; intros.
  induction H0; auto. destruct H1; inversion H.

  destruct H2. destruct H3; inversion H.
  eapply T3_5_4 with (t'' := y0) in H; auto.
  subst. 
  apply IHmulti; auto.
Qed.

Theorem T3_5_12 : forall t1,
    exists t', value t' /\ t1 -->* t'.
Proof.
  induction t1.
  exists true; split. apply v_true. apply multi_refl.
  exists false; split. apply v_false. apply multi_refl.
  inversion IHt1_1; inversion IHt1_2; inversion IHt1_3;
  clear IHt1_3; clear IHt1_2; clear IHt1_1.
  inversion H. inversion H0. inversion H1.
  induction H3.
  destruct H2.
  exists x0. split; auto. eapply multi_step. apply E_IfTrue. assumption.
  exists x1. split; auto. eapply multi_step. apply E_IfFalse. assumption.

  destruct IHmulti; auto.
  exists x2. inversion H9; split; auto.
  eapply multi_step. apply E_If. apply H3. assumption.
Qed.

End ArithBool.

Module ArithNat.


Inductive t: Type :=
| true
| false
| If (t1 t2 t3: t)
| O
| succ (t1: t)
| pred (t1: t)
| iszero (t1: t).


Inductive NatValue: t -> Prop :=
| nv_O : NatValue O
| nv_S : forall nv1, NatValue nv1 -> NatValue (succ nv1).

Inductive value: t -> Prop :=
| v_tru : value true
| v_fls : value false
| v_nat : forall t1, NatValue t1 -> value t1.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step: t -> t -> Prop :=
| E_IfTrue : forall t2 t3,
    If true t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If false t2 t3 --> t3
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
    iszero O --> true
| E_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) --> false
| E_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

  where " t '-->' t' " := (step t t').


Lemma nv_notstep : forall nv1,
    NatValue nv1 -> not (exists t1, nv1 --> t1).
Proof.
  intros. induction H; intro H1.
  inversion H1. inversion H.
  inversion H1. inversion H0; subst.
  induction IHNatValue.
  exists t1'; assumption.
Qed.

Theorem T3_5_14 : forall t1 t1' t1'',
    t1 --> t1' -> t1 --> t1'' -> t1' = t1''.
Proof.
  intros. generalize dependent t1''.
  induction H; intros.
  - (*E_IfTtur*)
    inversion  H0; subst; auto. inversion H4.
  - (*E_IfFalse*)

    inversion H0; subst; auto. inversion H4.
  - (*E_If*)
    inversion H0; subst. inversion H. inversion H.
    apply IHstep in H5; subst; auto.
  - (*E_Succ*)
    inversion H0. apply IHstep in H2; subst; auto.
  - (*E_PredZero*)
    inversion H0; subst; auto. inversion H1.
  - (*E_PredSucc*)
    inversion H0; auto.
    apply nv_notstep in H. inversion H2. induction H. exists t1'0. assumption.
  - (*E_Pred*)
    inversion H0; subst. inversion H.
    inversion H. apply nv_notstep in H2. induction H2. exists t1'0; auto. 
    apply IHstep in H2. subst; auto.
  - (*E_IsZeroZero*)
    inversion H0; subst; auto. inversion H1.
  - (*E_IsZeroSucc*)
    inversion H0; subst; auto.
    inversion H2; subst. apply nv_notstep in H. induction H. exists t1'0; auto.
  - (*E_Iszero*)
    inversion H0; subst.
    inversion H.
    apply nv_notstep in H2. induction H2. inversion H. exists t1'0; auto.
    apply IHstep in H2. subst; auto.
Qed.


Reserved Notation " t '==>' t' " (at level 40).

Inductive bigstep : t -> t -> Prop :=
| B_Value : forall t1,
    value t1 -> t1 ==> t1
| B_IfTrue : forall t1 t2 v2 t3,
    t1 ==> true -> t2 ==> v2 -> value v2 -> If t1 t2 t3 ==> v2
| B_IfFalse : forall t1 t2 t3 v3,
    t1 ==> false -> t3 ==> v3 -> value v3 -> If t1 t2 t3 ==> v3
| B_Succ : forall t1 nv1,
    t1 ==> nv1 -> NatValue nv1 -> succ t1 ==> succ nv1
| B_PredZero : forall t1,
    t1 ==> O -> pred t1 ==> O
| B_PredSucc : forall t1 nv1,
    t1 ==> (succ nv1) -> NatValue nv1 -> pred t1 ==> nv1
| B_IsZeroZero : forall t1,
    t1 ==> O -> iszero t1 ==> true
| B_IsZeroSucc : forall t1 nv1,
    t1 ==> (succ nv1) -> iszero t1 ==> false

  where " t '==>' t' " := (bigstep t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma bigstepvalue: forall t1 v,
    t1 ==> v -> value v.
Proof.
  intros. induction H; auto.
  apply v_nat. apply nv_S; auto.
  inversion IHbigstep. inversion H1. apply v_nat; auto.
  apply v_tru. apply v_fls.
Qed.

Lemma bigsteptrans: forall t1 t1' t2,
    t1 --> t1' -> t1' ==> t2 -> t1 ==> t2.
Proof.
  intros. generalize dependent t2; induction H; intros.
  - (*E_IfTrue*)
    apply B_IfTrue; auto. apply B_Value; apply v_tru.
    eapply bigstepvalue; auto. apply H0.
  - (*E_IfFalse*)
    apply B_IfFalse; auto. apply B_Value; apply v_fls.
    eapply bigstepvalue; eauto.
  - (*E_If*)
    inversion H0; subst. inversion H1. inversion H2.
    apply B_IfTrue; auto.
    apply B_IfFalse; auto.
  - (*E_Succ*)
    inversion H0; subst. inversion H1. inversion H2. apply B_Succ; auto.
    apply IHstep. apply B_Value; auto. apply v_nat; auto.
    apply B_Succ; auto.
  - (*E_PredZero*)
    inversion H0; subst. apply B_PredZero; auto.
  - (*E_PredSucc*)
    inversion H; subst.
    inversion H0. apply B_PredSucc; auto. apply B_Value. apply v_nat; apply nv_S; apply nv_O.
    inversion H0; subst. apply B_PredSucc. apply B_Value. apply v_nat; apply nv_S. apply H. auto.
    apply B_PredSucc. apply B_Succ; auto. apply nv_S; auto. apply nv_S; auto.
  - (*E_Pred*)
    inversion H0; subst. inversion H1. inversion H2.
    apply B_PredZero. apply IHstep; auto.
    apply B_PredSucc; auto. 
  - (*E_IsZeroZero*)
    inversion H0. apply B_IsZeroZero. apply B_Value. apply v_nat. apply nv_O.
  - (*E_IsZeroSucc*)
    inversion H0. apply B_IsZeroSucc with (nv1:= nv1). apply B_Value. apply v_nat; apply nv_S; auto.
  - (*E_IsZero*)
    inversion H0; subst. inversion H1. inversion H2.
    apply B_IsZeroZero; auto.
    apply B_IsZeroSucc with (nv1:= nv1); auto.
Qed.


Theorem T3_5_18 : forall t1 v,
    (t1 -->* v) -> value v -> t1 ==> v.
Proof.
  intros. induction H.
  apply B_Value; auto.
  pose proof (IHmulti H0).
  eapply bigsteptrans. apply H. apply H2.
Qed.

End ArithNat.

Module ArithNatBad.

Inductive t: Type :=
| tru
| fls
| If (t1 t2 t3: t)
| O
| succ (t1: t)
| pred (t1: t)
| iszero (t1: t)
| wrong.


Inductive NatValue: t -> Prop :=
| nv_O : NatValue O
| nv_S : forall nv1, NatValue nv1 -> NatValue (succ nv1).

Inductive value: t -> Prop :=
| v_tru : value tru
| v_fls : value fls
| v_nat : forall t1, NatValue t1 -> value t1.

Inductive BadNat : t -> Prop :=
| bn_tru : BadNat tru
| bn_fls : BadNat fls
| bn_wrong : BadNat wrong.

Inductive BadBool : t -> Prop :=
| bb_nat : forall t1, NatValue t1 -> BadBool t1
| bb_wrong : BadBool wrong.

Reserved Notation " t '-->' t' " (at level 40).
Inductive estep: t -> t -> Prop :=
| Ee_IfTrue : forall t2 t3,
    If tru t2 t3 --> t2
| Ee_IfFalse : forall t2 t3,
    If fls t2 t3 --> t3
| Ee_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3
| Ee_Succ : forall t1 t1',
    t1 --> t1' -> succ t1 --> succ t1'
| Ee_PredZero :
    pred O --> O
| Ee_PredSucc : forall nv1,
    NatValue nv1 -> pred (succ nv1) --> nv1
| Ee_Pred : forall t1 t1',
    t1 --> t1' -> pred t1 --> pred t1'
| Ee_IsZeroZero :
    iszero O --> tru
| Ee_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) --> fls
| Ee_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

(*行き詰まり処理*)
| Ee_IfWrong : forall t1 t2 t3,
    BadBool t1 -> If t1 t2 t3 --> wrong
| E_SuccWrong : forall t1,
    BadNat t1 -> succ t1 --> wrong
| Ee_PredWrong : forall t1,
    BadNat t1 -> pred t1 --> wrong
| Ee_IsZeroWrong : forall t1,
    BadNat t1 -> iszero t1 --> wrong

  where " t '-->' t' " := (estep t t').

Reserved Notation " t '-->o' t' " (at level 40).
Inductive step: t -> t -> Prop :=
| E_IfTrue : forall t2 t3,
    If tru t2 t3 -->o t2
| E_IfFalse : forall t2 t3,
    If fls t2 t3 -->o t3
| E_If : forall t1 t1' t2 t3,
    t1 -->o t1' ->
    If t1 t2 t3 -->o If t1' t2 t3
| E_Succ : forall t1 t1',
    t1 -->o t1' -> succ t1 -->o succ t1'
| E_PredZero :
    pred O -->o O
| E_PredSucc : forall nv1,
    NatValue nv1 -> pred (succ nv1) -->o nv1
| E_Pred : forall t1 t1',
    t1 -->o t1' -> pred t1 -->o pred t1'
| E_IsZeroZero :
    iszero O -->o tru
| E_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) -->o fls
| E_IsZero : forall t1 t1',
    t1 -->o t1' -> iszero t1 -->o iszero t1'

  where " t '-->o' t' " := (step t t').

Definition stop (t1: t) :=
  not (value t1) /\ not (exists t1', t1 -->o t1').

Lemma existstop:
  exists t1, stop t1.
Proof.
  exists (iszero tru).
  split.
  intro H; inversion H. inversion H0.
  intro H. inversion H. inversion H0. inversion H2.
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

Fixpoint Good (t1: t) : bool :=
  match t1 with
  | wrong => false
  | If t1' t2 t3 => andb (Good t1') (andb (Good t2) (Good t3))
  | succ t1' => Good t1'
  | pred t1' => Good t1'
  | iszero t1' => Good t1'
  | _ => true
  end.

Lemma nv_notstep : forall nv1,
    NatValue nv1 -> not (exists t1, nv1 --> t1).
Proof.
  intros. induction H; intro H1.
  inversion H1. inversion H.
  inversion H1. inversion H0; subst.
  induction IHNatValue.
  exists t1'; assumption.
  inversion H3; subst; solve_by_invert.
Qed.

Lemma NatValuesucc: forall nv,
    NatValue nv -> not (exists t1', succ nv --> t1').
Proof.
  intros. induction H.
  intro H. inversion H. inversion H0; try solve_by_invert.
  intro HH. inversion HH. inversion H0; subst.
  induction IHNatValue. exists t1'; auto.
  inversion H2.
Qed.

Lemma A3: forall t1 t1' t1'',
     t1 --> t1' -> t1 --> t1'' -> t1' = t1''.
Proof.
  intros. generalize dependent t1''; induction H; intros.
  -
    inversion H0; subst; auto; try solve_by_invert. inversion H4. inversion H.
  -
    inversion H0; subst; auto; try solve_by_inverts 2.
  -
    inversion H0; subst; try solve_by_invert.
    apply IHestep in H5; subst; auto.
    inversion H5; subst. induction (nv_notstep t1); auto. exists t1'; auto.
    inversion H.
  -
    inversion H0; subst. rewrite IHestep with (t1'':=t1'0); auto.
    inversion H2; subst; try solve_by_invert.
  -
    inversion H0; auto; try solve_by_invert.
  -
    inversion H0; subst; auto.
    induction (NatValuesucc nv1); auto. exists t1'; auto.
    inversion H2.
  -
    inversion H0;subst. inversion H.
    induction (NatValuesucc t1''); auto. exists t1'; auto. 
    apply IHestep in H2; subst; auto.
    inversion H2; subst; try solve_by_invert.
  -
    inversion H0; auto; try solve_by_invert.
  -
    inversion H0; subst; auto.
    induction (NatValuesucc nv1); auto. exists t1'; auto.
    inversion H2.
  -
    inversion H0; subst; auto; try solve_by_invert.
    induction (NatValuesucc nv1); auto. exists t1'; auto.
    apply IHestep in H2; subst; auto.
    inversion H2; subst; try solve_by_invert.
  -
    inversion H0; subst; try solve_by_inverts 2; auto.
    inversion H; subst; try solve_by_invert.
    induction (nv_notstep t1); auto. exists t1'; auto.
  -
    inversion H; subst.
    inversion H0; subst; try solve_by_invert; auto.
    inversion H0; subst; try solve_by_invert; auto.
    inversion H0; subst; auto. inversion H2.
  -
    inversion H0; subst; try solve_by_invert; auto.
    inversion H; subst; try solve_by_invert.
  -
    inversion H0; subst; try solve_by_invert; auto.
    inversion H; subst; try solve_by_invert.
Qed.


Lemma IfStopWrong: forall t1 t2 t3,
    stop (If t1 t2 t3) -> not (exists t1', t1 -->o t1').
Proof.
  intros.
  induction t1.
  - (*tur*)
    inversion H. induction H1. exists t2; apply E_IfTrue.
  - (*fls*)
    inversion H. induction H1; exists t3; apply E_IfFalse.
  - (*If*)
    intros HH.
    inversion HH.
    inversion H.
    inversion H0; subst;
    induction H2; eexists; eapply E_If; apply H0.
  -
    intro HH; inversion HH. inversion H0.
  -
    intro HH; inversion HH. inversion H0.
    inversion H. induction H5.
    eexists. eapply E_If. eapply E_Succ. apply H2.
  -
    intros HH; inversion HH. inversion H. inversion H0; subst;
    induction H2; subst; eexists; eapply E_If; eassumption.
  -
    intros HH; inversion HH; inversion H. inversion H0; subst;
    induction H2; eexists; eapply E_If; eassumption.
  -
    intros HH; inversion HH; inversion H. inversion H0; subst;
    induction H2; eexists; eapply E_If; eassumption.
Qed.

Notation multiestep := (multi estep).
Notation "t1 '-->*' t2" := (multiestep t1 t2) (at level 40).

Notation multistep := (multi step).
Notation "t1 '-->o*' t2" := (multistep t1 t2) (at level 40).


Lemma Iftrans : forall t1 t2 t3 t1',
    t1 -->* t1' -> If t1 t2 t3 -->* If t1' t2 t3.
Proof.
  intros. induction H.
  apply multi_refl. eapply multi_step. apply Ee_If. eassumption.
  assumption.
Qed.


Lemma multitrans: forall t1 t2 t3,
    t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros. generalize dependent t3. induction H; intros.
  assumption.
  eapply multi_step. apply H. apply IHmulti. assumption.
Qed.


Fixpoint NVBool (t1: t) : bool :=
  match t1 with
  | O => true
  | succ t1' => NVBool t1'
  | _ => false
  end.

Lemma NVB_nv : forall t1,
    NVBool t1 = true <-> NatValue t1.
Proof.
  split; intros.
  -
    induction t1; try solve_by_invert.
    apply nv_O. apply nv_S. apply IHt1. inversion H; auto.
  -
    induction H; subst; auto.
Qed.

Lemma stepe : forall t1 t1',
    t1 -->o t1' -> t1 --> t1'.
Proof.
  intros. induction H.
  -
    apply Ee_IfTrue.
  -
    apply Ee_IfFalse.
  -
    apply Ee_If; auto.
  -
    apply Ee_Succ; auto.
  -
    apply Ee_PredZero.
  -
    apply Ee_PredSucc; auto.
  -
    apply Ee_Pred; auto.
  -
    apply Ee_IsZeroZero.
  -
    apply Ee_IsZeroSucc; auto.
  -
    apply Ee_IsZero; auto.
Qed.

Lemma succtrans : forall t1 t1',
    t1 -->* t1' -> succ t1 -->* succ t1'.
Proof.
  intros. induction H.
  apply multi_refl.
  eapply multi_step. apply Ee_Succ. apply H. apply IHmulti.
Qed.

Lemma predtrans : forall t1 t1',
    t1 -->* t1' -> pred t1 -->* pred t1'.
Proof.
  intros. induction H.
  apply multi_refl.
  eapply multi_step. apply Ee_Pred; eassumption. auto.
Qed.

Lemma iszerotrans : forall t1 t1',
    t1 -->* t1' -> iszero t1 -->* iszero t1'.
Proof.
  intros. induction H.
  apply multi_refl.
  eapply multi_step. apply Ee_IsZero. apply H. auto.
Qed.


Lemma estepor: forall t1 t1',
    t1 --> t1' -> t1 -->o t1' \/ t1 -->* wrong.
Proof.
  induction t1; intros; try solve_by_invert.
  -
    inversion H; subst.
    left. apply E_IfTrue.
    left. apply E_IfFalse.
    apply IHt1_1 in H4; inversion H4.
    left. apply E_If; auto.
    apply Iftrans with (t2:= t1_2) (t3:=t1_3) in H0.
    right. eapply multitrans. apply H0. eapply multi_step. apply Ee_IfWrong. apply bb_wrong. apply multi_refl.
    right. eapply multi_step. apply H. apply multi_refl.
  -
    inversion H; subst. apply IHt1 in H1. inversion H1.
    left. apply E_Succ; auto.
    apply succtrans in H0. right. eapply multitrans. apply H0. eapply multi_step. apply E_SuccWrong. apply bn_wrong. apply multi_refl.
    right. eapply multi_step. apply H. apply multi_refl.
  -
    inversion H; subst.
    left. apply E_PredZero. left. apply E_PredSucc; auto.
    apply IHt1 in H1. inversion H1. left. apply E_Pred; auto.
    right. apply predtrans in H0. eapply multitrans. apply H0. eapply multi_step. apply Ee_PredWrong. apply bn_wrong. apply multi_refl.
    right. eapply multi_step. apply Ee_PredWrong; auto. apply multi_refl.
  -
    inversion H; subst.
    left. apply E_IsZeroZero. left. apply E_IsZeroSucc; auto.
    apply IHt1 in H1. inversion H1.
    left. apply E_IsZero; auto.
    right. apply iszerotrans in H0. eapply multitrans. apply H0. eapply multi_step. apply Ee_IsZeroWrong. apply bn_wrong. apply multi_refl.
    right. eapply multi_step. apply Ee_IsZeroWrong; auto. apply multi_refl.
Qed.

Fixpoint isnumericval (t1: t): bool :=
  match t1 with
  | O => true
  | succ t1 => isnumericval t1
  | _ => false
  end.

Fixpoint isval (t1: t) : bool :=
  match t1 with
  | tru => true
  | fls => true
  | _ => isnumericval t1
  end.

Definition isbool (t1: t) : bool :=
  match t1 with
  | tru => true
  | fls => true
  | _ => false
  end.

Definition isBNat (t1: t) : bool :=
  match t1 with
  | wrong => true
  | _ => isbool t1
  end.

Definition isBbool (t1: t) : bool :=
  match t1 with
  | wrong => true
  | _ => isnumericval t1
  end.


Inductive optiont : Type :=
| Some (T: t)
| None.


Fixpoint eval1 (t': t) : optiont :=
  match t' with
  | If t1 t2 t3 =>
    if (isbool t1) then
      match t1 with
      | tru => Some t2
      | fls => Some t3
      | _ => None
      end else if (isBbool t1) then Some wrong else
      match (eval1 t1) with
      | Some t1' => Some (If t1' t2 t3)
      | _ => None
      end
  | succ t1 =>
    if isnumericval t1 then
      None else if (isBNat t1) then Some wrong else
      match (eval1 t1) with
      | Some t1' => Some (succ t1')
      | _ => None
      end
  | pred t1 =>
    if (isnumericval t1) then
      match t1 with
      | O => Some O
      | succ nv1 => Some nv1
      | _ => None
      end else if (isBNat t1) then Some wrong else
      match (eval1 t1) with
      | Some t1' => Some (pred t1')
      | _ => None
      end
  | iszero t1 =>
    if (isnumericval t1) then
      match t1 with
      | O => Some tru
      | succ _ => Some fls
      | _ => None
      end else if (isBNat t1) then Some wrong else
      match (eval1 t1) with
      | Some t1' => Some (iszero t1')
      | _ => None
      end
  | _ => None
  end.

Lemma isnumericvalCC : forall t1,
    isnumericval t1 = true <-> NatValue t1.
Proof.
  split; intros.
  induction t1; try solve_by_invert.
  apply nv_O. inversion H. apply nv_S. apply IHt1; auto.
  induction H. reflexivity. inversion IHNatValue; auto.
Qed.

Lemma NVstep: forall nv,
    NatValue nv -> not (exists t1', succ nv -->o t1').
Proof.
  intros. induction H.
  intro H. inversion H. inversion H0; try solve_by_invert.
  intro HH. inversion HH. inversion H0; subst.
  induction IHNatValue. exists t1'; auto.
Qed.


Lemma BBCC : forall t1,
    isBbool t1 = true <-> BadBool t1.
Proof.
  split; intros.
  induction t1; try solve_by_inverts 2. apply bb_nat. apply nv_O. apply bb_nat. apply nv_S.
  inversion H. apply isnumericvalCC in H1. auto. apply bb_wrong.
  induction H; auto. induction H; auto. simpl. apply isnumericvalCC. auto.
Qed.

Lemma BNCC : forall t1,
    isBNat t1 = true <-> BadNat t1.
Proof.
  split; intros.
  induction t1; try solve_by_invert. apply bn_tru. apply bn_fls. apply bn_wrong.
  inversion H; auto.
Qed.

Lemma eval1OK : forall t1 t1',
    t1 --> t1' <-> eval1 t1 = Some t1'.
Proof with eauto.
  split; intros.
  -
    induction H; try reflexivity; simpl.
    +
      destruct (isbool t1) eqn:IHb.
      destruct t1; try solve_by_invert.
      destruct (isBbool t1) eqn:IHBb.
      unfold isbool in IHb. unfold isBbool in IHBb.
      destruct t1; try solve_by_invert.
      apply isnumericvalCC in IHBb.
      inversion IHBb; subst.
      inversion H. subst. induction (nv_notstep t1); auto. exists t1'0. auto.
      subst. destruct t1; try solve_by_invert.
      rewrite IHestep. reflexivity.
    +
      destruct (isnumericval t1) eqn:IHn.
      destruct t1; try solve_by_invert. apply isnumericvalCC in IHn.
      inversion IHn; subst. induction (nv_notstep t1); auto. inversion H; subst. exists t1'0; auto.
      destruct t1; try solve_by_invert.
      destruct (isBNat t1) eqn:IHBn. destruct t1; try solve_by_invert.
      rewrite IHestep; auto.
    +
      apply isnumericvalCC in H. rewrite H. auto.
    +
      rewrite IHestep. destruct (isnumericval t1) eqn:IHnum. apply isnumericvalCC in IHnum.
      induction (nv_notstep t1); auto. exists t1'; auto.
      destruct (isBNat t1) eqn:IHBN. destruct t1; try solve_by_invert.
      auto.
    +
      apply isnumericvalCC in H. rewrite H. auto.
    +
      rewrite IHestep. destruct (isnumericval t1) eqn:IHn. destruct t1; try solve_by_invert.
      inversion H; subst. apply isnumericvalCC in IHn. inversion IHn; subst. induction (nv_notstep t1); auto.
      exists t1'0; auto.
      destruct t1; try solve_by_invert.
      destruct (isBNat t1) eqn:IHB; auto. destruct t1; try solve_by_invert.
    +
      destruct (isbool t1) eqn:IHb. destruct t1; try solve_by_inverts 2.
      apply BBCC in H. rewrite H; auto.
    +
      destruct (isnumericval t1) eqn:IHnum. destruct t1; try solve_by_invert.
      apply BNCC in H. rewrite H. auto.
    +
      destruct t1; try solve_by_invert; auto.
    +
      destruct t1; try solve_by_invert; auto.
  -
    generalize dependent t1'.
    induction t1; intros; try solve_by_invert.
    +
      inversion H. destruct (isbool t1_1) eqn:IHB. destruct t1_1; try solve_by_invert; inversion H1; constructor.
      induction (isBbool t1_1) eqn:IHBB. inversion H1. apply Ee_IfWrong. apply BBCC in IHBB. auto.
      induction (eval1 t1_1); inversion H1. apply Ee_If. apply IHt1_1. reflexivity.
    +
      inversion H. destruct (isnumericval t1) eqn:IHnum; try solve_by_invert.
      destruct (isBNat t1) eqn:IHBN. inversion H1. apply E_SuccWrong. apply BNCC; auto.
      destruct (eval1 t1); inversion H1. apply Ee_Succ. apply IHt1...
    +
      inversion H. destruct (isnumericval t1) eqn:IHnum. destruct t1; try solve_by_invert; inversion H1.
      apply Ee_PredZero. apply Ee_PredSucc. inversion IHnum. subst. apply isnumericvalCC...
      destruct (isBNat t1) eqn:IHBN. inversion H1. apply Ee_PredWrong. apply BNCC...
      destruct (eval1 t1); inversion H1. apply Ee_Pred; apply IHt1...
    +
      inversion H. destruct (isnumericval t1) eqn:IHn. destruct t1; inversion H1.
      apply Ee_IsZeroZero. apply Ee_IsZeroSucc. apply isnumericvalCC...
      destruct (isBNat t1) eqn:IHB; inversion H1. apply Ee_IsZeroWrong. apply BNCC...
      destruct (eval1 t1); inversion H1. apply Ee_IsZero. apply IHt1...
Qed.


Inductive multieval :t -> t -> Prop :=
  | refl : forall t1, multieval t1 t1
  | st : forall t1 t1' t1'', eval1 t1 = Some t1' -> multieval t1' t1'' -> multieval t1 t1''.

Lemma multievalstep : forall t1 t1',
    multieval t1 t1' <-> t1 -->* t1'.
Proof.
  split; intros.
  -
    induction H. apply multi_refl.
    apply eval1OK in H. eapply multi_step. apply H; auto. apply IHmultieval.
  -
    induction H. apply refl. apply eval1OK in H. eapply st. apply H. apply IHmulti.
Qed.


Lemma A4: forall t1,
    stop t1 -> multieval t1 wrong.
Proof with eauto.
  induction t1; intros.
  -
    inversion H. induction H0. constructor.
  -
    inversion H. induction H0. constructor.
  -
    destruct (isbool t1_1) eqn:IHB. destruct t1_1; inversion IHB.
    inversion H. induction H1. exists t1_2. apply E_IfTrue.
    inversion H. induction H1. exists t1_3. constructor.
    destruct (isBbool t1_1) eqn:IHBb...
    apply st with (t1':= wrong). simpl. rewrite IHB. rewrite IHBb... apply refl.

    assert (stop t1_1).
    split; intro HH. inversion H. destruct t1_1; try solve_by_inverts 2.
    inversion HH. apply isnumericvalCC in H2.
    inversion IHBb. inversion H2. rewrite H5 in H6. inversion H6.
    inversion HH. inversion H. induction H2. exists (If x t1_2 t1_3). constructor; auto.

    apply IHt1_1 in H0. apply multievalstep in H0. apply multievalstep. apply Iftrans with (t2:= t1_2) (t3:=t1_3) in H0. eapply multitrans. apply H0. eapply multi_step. apply Ee_IfWrong. apply bb_wrong. apply multi_refl.
  -
    inversion H. induction H0; constructor. constructor.
  -
    destruct (isnumericval t1) eqn:IHnum. inversion H. induction H0. apply v_nat.
    apply nv_S; apply isnumericvalCC...
    destruct (isBNat t1) eqn: IHBn...
    eapply st with (t1':=wrong). simpl. rewrite IHBn. rewrite IHnum... constructor.

    assert (stop t1).
    split; intros HH. destruct t1; try solve_by_inverts 2. inversion HH. apply isnumericvalCC in H0. rewrite H0 in IHnum. inversion IHnum.
    inversion HH. inversion H. induction H2. exists (succ x). constructor. auto.

    apply IHt1 in H0. apply multievalstep in H0. apply multievalstep.
    apply succtrans in H0. eapply multitrans.
    apply H0.
    eapply multi_step. apply E_SuccWrong. apply bn_wrong. constructor.
  -
    simpl. destruct (isnumericval t1) eqn:IHnum. destruct t1; try solve_by_invert...
    inversion H. induction H1. exists O. constructor. inversion H. induction H1. exists t1. constructor. apply isnumericvalCC...
    destruct (isBNat t1) eqn:IHBn...
    eapply st with (t1':=wrong). simpl. rewrite IHBn. rewrite IHnum... constructor.

    assert (stop t1).
    split; intro HH. destruct t1; try solve_by_inverts 2. inversion HH. apply isnumericvalCC in H0. rewrite IHnum in H0. inversion H0.
    inversion HH. inversion H. induction H2. exists (pred x); constructor...
    apply IHt1 in H0. apply multievalstep. apply multievalstep in H0. apply predtrans in H0.
    eapply multitrans. apply H0. eapply multi_step. apply Ee_PredWrong. constructor. constructor.
  -
    simpl. destruct (isnumericval t1) eqn:IHnum. destruct t1; try solve_by_invert.
    inversion H. induction H1. exists tru; constructor. inversion H. induction H1. exists fls. constructor. apply isnumericvalCC...
    destruct (isBNat t1) eqn:BN...
    apply st with (t1':= wrong). simpl. rewrite IHnum. rewrite BN... constructor.

    assert (stop t1).
    split; intro HH. destruct t1; try solve_by_inverts 2. inversion HH. apply isnumericvalCC in H0. rewrite H0 in IHnum. inversion IHnum.
    inversion HH. inversion H. induction H2. exists (iszero x). constructor...
    apply IHt1 in H0.
    apply multievalstep in H0. apply multievalstep.
    apply iszerotrans in H0. eapply multitrans. apply H0.
    econstructor. apply Ee_IsZeroWrong. apply bn_wrong. constructor.
  -
    apply refl.
Qed.


Lemma A5: forall t1 t2,
    Good t1 = true -> Good t2 = false ->
    t1 --> t2 -> stop t1.
Proof.
  intros. induction H1; try solve_by_invert.
  -
    inversion H. apply andb_prop in H2. inversion H2. rewrite H1 in H0. discriminate H0.
  -
    inversion H. apply andb_prop in H2. inversion H2. rewrite H3 in H0; discriminate.
  -
    split; intros HH. inversion HH. inversion H2.
    inversion H0. inversion H. apply andb_prop in H4. inversion H4. rewrite H5 in H3.
    destruct (Good t1') eqn:IHH. discriminate.
    inversion HH. inversion H6; subst; try solve_by_invert.
    destruct IHestep; auto. induction H8. exists t1'0; auto.
  -
    split; intro HH. inversion HH; subst. inversion H2; induction (nv_notstep t1); auto. exists t1'; auto.
    inversion HH. inversion H2; subst. destruct IHestep; auto. induction H5. exists t1'0; auto.
  -
    inversion H. rewrite H3 in H0. inversion H0.
  -
    inversion H. destruct IHestep; auto.
    split; intro HH. inversion HH. inversion H5.
    inversion HH. inversion H5; subst; try solve_by_invert.
    induction H2. apply v_nat; apply nv_S; auto.
    induction H4. exists t1'0; auto.
  -
    inversion H; inversion H0. destruct IHestep; auto.
    split; intro HH. inversion HH. inversion H6.
    inversion HH. inversion H6; subst; try solve_by_invert.
    induction H2. apply v_nat; apply nv_S; auto.
    induction H5. exists t1'0; auto.
  -
    inversion H1; subst; try solve_by_inverts 2.
    split; intro HH; inversion HH. inversion H3.
    inversion H3; subst; try solve_by_invert.
    induction (NVstep t1); auto. exists (succ t1'). apply E_Succ; auto.
  -
    inversion H1; subst; try solve_by_invert;
    split; intro HH;
      inversion HH; inversion H2; subst; try solve_by_invert.
  -
    inversion H1; subst; try solve_by_invert;
      split; intro HH; inversion HH;  try solve_by_inverts 2.
  -
    inversion H1; subst; try solve_by_invert;
      split; intro HH; inversion HH;  try solve_by_inverts 2.
Qed.

Theorem A2right : forall t1 t1',
    Good t1 = true -> Good t1' = true ->
    t1 -->o t1' -> stop t1' -> t1 -->* wrong.
Proof.
  intros.
  eapply multi_step. apply stepe in H1. apply H1. apply multievalstep. apply A4. assumption.
Qed.

Theorem A2left : forall t1 t1',
    Good t1 = true -> Good t1' = true ->
    t1 -->o t1' -> t1' --> wrong -> stop t1'.
Proof.
  intros. split; intro HH.
  inversion HH; subst; try solve_by_inverts 2.
  induction (nv_notstep t1'); auto. exists wrong; auto.
  inversion HH. inversion H2; subst; try solve_by_invert.
  -
    inversion H0. apply andb_prop in H5. inversion H5. inversion H6.
  -
    inversion H4; subst. inversion H5; subst. inversion H3. inversion H10.
    inversion H3; subst. inversion H11; subst. induction (nv_notstep nv1); auto. eexists. apply stepe in H8. apply H8.
    inversion H3; subst. inversion H9.
  -
    inversion H4; subst; try solve_by_inverts 2.
  -
    inversion H4; subst; try solve_by_inverts 2.
  -
    inversion H4; subst; try solve_by_inverts 2.
Qed.



End ArithNatBad.

