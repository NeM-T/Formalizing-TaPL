Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
From Coq Require Import Lists.List.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Import ListNotations.

Module deBruijin.

Module E11_1.
Require Import Nat.

Inductive ty : Type :=
| Bool
| Arrow (T1 T2: ty)
| Unit.
Notation "t1 '|-->' t2" := (Arrow t1 t2) (at level 40).

Inductive term : Type :=
(*純粋λ計算*)
| var (n: nat)
| abs (name: string) (typ: ty) (t: term)
| app (t1 t2: term)

(*ぶーる*)
| tru
| fls
| If (t1 t2 t3: term)
(*拡張*)
| unit
| seq (t1 t2: term).

Inductive value : term -> Prop :=
  | v_abs : forall x T t, value (abs x T t)
  | v_tru : value tru
  | v_fls : value fls
  | v_unit: value unit.

Definition isval t :=
  match t with
  | tru => true
  | fls => true
  | abs _ _ _ => true
  | unit => true
  | _ => false
  end.

Fixpoint eqb_ty (T1 T2: ty) : bool :=
  match (T1, T2) with
  | (Bool, Bool) => true
  | (Unit, Unit) => true
  | (T11 |--> T12, T21 |--> T22) =>
    andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _ => false
  end.

Lemma eq_type_refl : forall T,
    eqb_ty T T = true.
Proof.
  induction T; simpl; auto. rewrite IHT1, IHT2; auto.
Qed.

Definition context := list (string * ty).
Definition eqb_string s1 s2:= String.eqb s1 s2.

Fixpoint getbinding (n : nat) (ctx: context) :=
  match n with
  | 0 =>
    match ctx with
    | [] => None
    | (x, t) :: ctx' => Some t
    end
  | S n' =>
    match ctx with
    | [] => None
    | x :: ctx' => getbinding n' ctx'
    end
  end.

Fixpoint shift (d : nat) (t : term) : term :=
match t with
| var x => var (if leb d x then (S x) else x)
| abs x T t' => abs x T (shift (S d) t')
| app t1 t2 => app (shift d t1) (shift d t2)
| tru => tru
| fls => fls
| If t1 t2 t3 =>
  If (shift d t1) (shift d t2) (shift d t3)
| unit => unit
| seq t1 t2 =>
  seq (shift d t1) (shift d t2)
end.

Fixpoint subst (d : nat) (s t: term) : term :=
match t with
| var x =>
  if eqb d x then s
  else if ltb d x then var (pred x) else var x
| abs x T t' => abs x T (subst (S d) (shift 0 s) t')
| app t1 t2 => app (subst d s t1) (subst d s t2)
| tru => tru
| fls => fls
| unit => unit
| If t1 t2 t3 =>
  If (subst d s t1) (subst d s t2) (subst d s t3)
| seq t1 t2 =>
  seq (subst d s t1) (subst d s t2)
end.

Reserved Notation " t '-->i' t' " (at level 40).
Inductive internal_step :term -> term -> Prop :=
| Ei_IfTrue : forall t2 t3,
    If tru t2 t3 -->i t2
| Ei_IfFalse : forall t2 t3,
    If fls t2 t3 -->i t3
| Ei_If : forall t1 t1' t2 t3,
    t1 -->i t1' ->
    If t1 t2 t3 -->i If t1' t2 t3
| Ei_App1 : forall t1 t2 t1',
    t1 -->i t1' ->
    app t1 t2 -->i app t1' t2
| Ei_App2 : forall v1 t2 t2',
    value v1 ->
    t2 -->i t2' ->
    app v1 t2 -->i app v1 t2'
| Ei_AppAbs : forall typ str t12 t2,
    value t2 ->
    app (abs str typ t12) t2 -->i subst 0 t2 t12

where " t '-->i' t' " := (internal_step t t').

Reserved Notation " t '-->e' t' " (at level 40).
Inductive external_step : term -> term -> Prop :=
| E_IfTrue : forall t2 t3,
    If tru t2 t3 -->e t2
| E_IfFalse : forall t2 t3,
    If fls t2 t3 -->e t3
| E_If : forall t1 t1' t2 t3,
    t1 -->e t1' ->
    If t1 t2 t3 -->e If t1' t2 t3
| E_App1 : forall t1 t2 t1',
    t1 -->e t1' ->
    app t1 t2 -->e app t1' t2
| E_App2 : forall v1 t2 t2',
    value v1 ->
    t2 -->e t2' ->
    app v1 t2 -->e app v1 t2'
| E_AppAbs : forall typ str t12 t2,
    value t2 ->
    app (abs str typ t12) t2 -->e subst 0 t2 t12
| E_seq : forall t1 t1' t2,
    t1 -->e t1' ->
    seq t1 t2 -->e seq t1' t2
| E_SeqNext : forall v1 t2,
    value v1 ->
    seq v1 t2 -->e t2
where " t '-->e' t' " := (external_step t t').

Lemma leb_S_l : forall m n,
  leb (n + S m) n = false.
Proof.
  induction n; simpl; intros; auto.
Qed.

Require Import PeanoNat.

Lemma sub_shift : forall t1 t2 n,
    subst n t2 (shift n t1) = t1.
Proof.
  induction t1; intros; simpl; auto.
  -
    destruct leb eqn:IH1; destruct eqb eqn:IH2; try apply Nat.eqb_eq in IH2; subst.
    apply Nat.leb_le in IH1. apply Nat.nle_succ_diag_l in IH1. inversion IH1.
    apply Nat.leb_le in IH1. apply Lt.le_lt_n_Sm in IH1. apply Nat.ltb_lt in IH1. rewrite IH1. simpl. reflexivity.
    rewrite Nat.leb_refl in IH1. inversion IH1.
    assert (n0 <? n = false).
    apply Nat.ltb_ge, Nat.lt_le_incl, Nat.leb_gt. apply IH1.
    rewrite H. reflexivity.
  -
    rewrite IHt1. reflexivity.
  -
    rewrite IHt1_1, IHt1_2; reflexivity.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  -
    rewrite IHt1_2, IHt1_1; reflexivity.
Qed.

Notation "t1 ';' t2" := (seq t1 t2) (at level 50).

Fixpoint e2t t :=
  match t with
  | var x => var x
  | abs x T t' => abs x T (e2t t')
  | app t1 t2 => app (e2t t1) (e2t t2)
  | If t1 t2 t3 => If (e2t t1) (e2t t2) (e2t t3)
  | t1; t2 => app (abs "x" Unit (shift 0 (e2t t2 ))) (e2t t1)
  | _ => t
  end.

Lemma shift_shift : forall t1 i k,
    i < (S k) ->
    shift (S k) (shift i t1 ) = shift i (shift k t1).
Proof.
  induction t1; simpl; intros; auto.
  -
    destruct leb eqn:IH1; destruct (leb k n) eqn:IH2.
    apply Nat.leb_le in IH1. apply le_S in IH1. apply Nat.leb_le in IH1. rewrite IH1. reflexivity.
    rewrite IH1. reflexivity.

    destruct n. apply Nat.leb_le in IH2. inversion IH2; subst. compute in H. apply le_S_n in H.
    inversion H; subst. simpl in IH1. inversion IH1.

    compute in H. apply le_S_n in H. apply Nat.leb_le in IH2. apply Nat.le_trans with (p:= (S n)) in H; auto.
    apply Nat.leb_nle in IH1. apply IH1 in H. inversion H.
    rewrite IH1.
    destruct n; auto.
    assert (k <=? n = false).
    +
      apply Nat.leb_nle. intro. apply le_S in H0. apply Nat.leb_nle in IH2. apply IH2. apply H0.
    +
    rewrite H0. reflexivity.
  -
    rewrite IHt1; auto. apply Lt.lt_n_S. apply H.
  -
    rewrite IHt1_1, IHt1_2; auto.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; auto.
  -
    rewrite IHt1_1, IHt1_2; auto.
Qed.


Notation "t1 '[[' n ':=' t2 ']]' " := (subst n t2 t1) (at level 20).
Lemma shift_sub : forall t1 i j s,
    j < (S i) ->
    shift i (t1 [[ j := s]] ) = (shift (i + 1 ) t1) [[j := (shift i s) ]].
Proof.
  induction t1; simpl; intros; auto.
  -
    rewrite Nat.add_1_r.
    destruct eqb eqn:IH1.
    +
      apply Nat.eqb_eq in IH1; subst.
      apply Nat.nle_gt in H. apply Nat.leb_nle in H. rewrite H.
      rewrite Nat.eqb_refl. reflexivity.
    +
      destruct ((S i) <=? n) eqn:IH2; simpl.
      ++
        apply Nat.leb_le in IH2. apply Nat.lt_le_trans with (p:= n) in H; auto. apply Nat.ltb_lt in H.
        rewrite H; simpl.
        destruct n. inversion H. simpl.
        apply le_S_n in IH2. apply Nat.leb_le in IH2. rewrite IH2.
        destruct (j =? (S(S n))) eqn:IH3. apply Nat.eqb_eq in IH3; subst.
        apply Nat.ltb_lt in H. apply Nat.nlt_succ_diag_l in H. inversion H.
        apply Nat.ltb_lt, Nat.lt_lt_succ_r, Nat.ltb_lt in H. rewrite H.
        reflexivity.
      ++
        destruct (j <? n) eqn:IH3.
        +++
          rewrite IH1. simpl. destruct n; simpl. compute in H. apply le_S_n in H. destruct i; simpl; auto.
          inversion H; subst. simpl in IH1. inversion IH1.
          apply Nat.leb_nle, Nat.nle_gt, Lt.lt_S_n, Nat.nle_gt, Nat.leb_nle in IH2.
          rewrite IH2. reflexivity.
        +++
          simpl. rewrite IH1.
          apply Nat.leb_nle, Nat.nle_gt in IH2. compute in IH2.
          apply le_S_n, Lt.le_lt_or_eq in IH2. destruct IH2.
          apply Nat.nle_gt in H0. apply Nat.leb_nle in H0. rewrite H0; reflexivity.
          subst. compute in H. apply le_S_n, Lt.le_lt_or_eq in H. destruct H.
          apply Nat.ltb_lt in H. rewrite H in IH3. inversion IH3.
          subst. rewrite Nat.eqb_refl in IH1. inversion IH1.
  -
    rewrite IHt1. rewrite shift_shift; auto.
    apply Nat.lt_0_succ.
    apply Lt.lt_n_S; auto.
  -
    rewrite IHt1_1, IHt1_2; auto.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; auto.
  -
    rewrite IHt1_1, IHt1_2; auto.
Qed.

Lemma shift_sub_lt : forall t1 s i j,
    i < (S j) ->
    shift i (t1 [[j := s]]) = (shift i t1) [[(S j) := shift i s]].
Proof.
 induction t1; simpl; intros; auto.
   -
    destruct eqb eqn:IH1.
    +
      apply Nat.eqb_eq in IH1; subst.
      destruct leb eqn:IH2.
      *
        simpl. rewrite Nat.eqb_refl. reflexivity.
      *
        apply Nat.leb_nle in IH2. compute in H. apply le_S_n in H. induction IH2; auto.
    +
      destruct (j <? n) eqn:IH2.
      *
        destruct (i <=? n) eqn:IH3.
        **
          rewrite IH1. apply Nat.ltb_lt in IH2. apply Lt.lt_n_S in IH2. apply Nat.ltb_lt in IH2.
          rewrite IH2. simpl. destruct n; try discriminate; simpl.
          apply Nat.leb_le in IH3. apply Lt.le_lt_or_eq in IH3. destruct IH3; subst.
          compute in H0. apply le_S_n in H0. apply Nat.leb_le in H0; rewrite H0. reflexivity.
          apply Nat.ltb_lt in IH2. apply Lt.lt_S_n in IH2. apply Lt.lt_S_n in H.
          apply Nat.nle_gt in IH2. compute in H. induction IH2. apply H.
        **
          destruct n; try discriminate; simpl.
          apply Nat.leb_nle in IH3. apply Nat.nle_gt in IH3. apply Nat.lt_succ_l in IH3. apply Nat.nle_gt in IH3. apply Nat.leb_nle in IH3. rewrite IH3.
          destruct (j =? n) eqn:IH4. apply Nat.eqb_eq in IH4; subst. compute in H. apply Nat.leb_nle in IH3. apply le_S_n in H. induction IH3; apply H.
          destruct (S j <? S n) eqn:IH5; auto.
          apply Nat.ltb_lt in IH2. compute in IH2. apply Lt.le_lt_or_eq in IH2. destruct IH2; subst; try discriminate.
          apply Nat.ltb_lt in H0. rewrite H0 in IH5. inversion IH5. inversion H0; subst. rewrite Nat.eqb_refl in IH4. inversion IH4.
      *
        destruct leb eqn:IH3.
        **
          rewrite IH1. simpl. rewrite IH3. destruct (S j <? S n) eqn:IH4; auto.
          apply Nat.ltb_lt, Lt.lt_S_n, Nat.ltb_lt in IH4. rewrite IH4 in IH2. inversion IH2.
        **
          destruct n; simpl. rewrite IH3. reflexivity.
          rewrite IH3. destruct (j =? n) eqn:IH4.
          apply Nat.eqb_eq in IH4; subst. apply Nat.ltb_nlt in IH2. apply Nat.nlt_ge in IH2. einduction Nat.nle_succ_diag_l. apply IH2.
          destruct (S j <? S n) eqn:IH5; auto.
          apply Nat.ltb_lt in IH5. compute in IH5. repeat apply Le.le_Sn_le in IH5.
          apply Lt.le_lt_or_eq in IH5; destruct IH5; subst. apply Nat.ltb_lt in H0. rewrite H0 in IH2. inversion IH2.
          rewrite Nat.eqb_refl in IH1. inversion IH1.
  -
    rewrite IHt1; auto. rewrite shift_shift; auto.
    apply Nat.lt_0_succ.
    apply Lt.lt_n_S; auto.
  -
    rewrite IHt1_1; try rewrite IHt1_2; auto.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; auto.
  -
    rewrite IHt1_1, IHt1_2; auto.
Qed.

Lemma subsub :forall t1 j i v u,
    i < (S j) ->
    t1[[ S j := shift i v ]] [[i := u[[j := v ]] ]] = t1 [[i := u ]] [[j := v]].
Proof.
  induction t1; simpl; intros; auto.
  -
    destruct n.
    +
      destruct ltb eqn:IH1. inversion IH1.
      simpl. destruct i. reflexivity.
      simpl. apply Lt.lt_S_n in H. destruct j. inversion H. simpl. reflexivity.
    +
      simpl.
      destruct eqb eqn:IH1.
      ++
        apply Nat.eqb_eq in IH1; subst. generalize H; intros. compute in H. destruct eqb eqn:IH1; try apply Nat.eqb_eq in IH1; subst.
        einduction Nat.nle_succ_diag_l; eauto. apply Nat.ltb_lt in H0. rewrite H0. simpl. rewrite Nat.eqb_refl.
        rewrite sub_shift. reflexivity.
      ++
        destruct ltb eqn:IH2; simpl.
        destruct (eqb i n) eqn:IH3. apply Nat.eqb_eq in IH3; subst.
        apply Nat.ltb_lt in IH2.
        apply Nat.nle_gt in IH2. compute in H. induction IH2. apply H.
      --
        destruct (ltb i n) eqn:IH4.
        destruct (i =? S n) eqn:IH5; try apply Nat.eqb_eq in IH5; subst. apply Nat.ltb_lt in IH4.
        induction (Nat.nlt_succ_diag_l n); apply IH4.
        apply Nat.ltb_lt in IH2. apply Nat.lt_trans with (p:= S n) in H; auto. apply Nat.ltb_lt in H. rewrite H.
        simpl. rewrite IH1. apply Lt.lt_S_n in IH2. apply Nat.ltb_lt in IH2. rewrite IH2. reflexivity.
        destruct (i =? S n) eqn:IH5; try apply Nat.eqb_eq in IH5; subst.
        apply Nat.ltb_lt in IH2. apply Nat.nle_gt in IH2. apply Nat.lt_le_incl in H. induction IH2. apply H.
        apply Nat.ltb_lt in IH2. apply Nat.lt_trans with (p:= S n) in H; auto. compute in H.
        apply le_S_n in H. apply Lt.le_lt_or_eq in H. destruct H.
        apply Nat.ltb_lt in H. rewrite H in IH4. inversion IH4.
        subst. rewrite Nat.eqb_refl in IH3. inversion IH3.
      --
        destruct (i =? S n) eqn:IH3; try apply Nat.eqb_eq in IH3; subst; auto.
        apply Nat.ltb_nlt in IH2. apply Nat.nlt_ge in IH2.
        destruct (i <? S n) eqn:IH4. simpl.
        rewrite IH1. apply le_S_n in IH2. apply Nat.nlt_ge in IH2. apply Nat.ltb_nlt in IH2. rewrite IH2. reflexivity.
        simpl.
        destruct (eqb j (S n)) eqn:IH5; try apply Nat.eqb_eq in IH5; subst.
        ***
          compute in H. apply le_S_n in H. apply Lt.le_lt_or_eq in H. destruct H; subst.
          apply Nat.ltb_nlt in IH4. induction IH4; apply H.
          rewrite Nat.eqb_refl in IH3. inversion IH3.
        ***
          destruct (ltb j (S n)) eqn:IH6; auto.
          apply Nat.ltb_lt in IH6. compute in IH6.
          apply Nat.lt_le_trans with (p:= S n) in H; auto. apply Nat.ltb_lt in H. rewrite H in IH4.
          inversion IH4.
  -
    generalize Nat.lt_0_succ; intros.
    generalize H; intros.
    apply Lt.lt_n_S in H. apply IHt1 with (v:= v) (u:= u) in H.
    rewrite shift_sub_lt; auto. rewrite <- shift_shift; auto. rewrite IHt1. reflexivity. apply Lt.lt_n_S.
    apply H1.
  -
    rewrite IHt1_2, IHt1_1; auto.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; auto.
  -
    rewrite IHt1_2, IHt1_1; auto.
Qed.

Lemma shift_e2t : forall t1 n,
    e2t (shift n t1) = shift n (e2t t1).
Proof.
  induction t1; simpl; intros; auto.
  -
    rewrite IHt1; reflexivity.
  -
    rewrite IHt1_1, IHt1_2; reflexivity.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  -
    rewrite shift_shift; auto.
    rewrite IHt1_1. rewrite IHt1_2. reflexivity.
    compute. apply le_n_S. apply le_0_n.
Qed.    

Lemma subst_e2t : forall t1 t2 n,
   e2t (t1[[n := t2]] ) = (e2t t1)[[n:= (e2t t2)]].
Proof.
  induction t1; simpl; intros; auto.
  -
    destruct eqb; destruct ltb; auto.
  -
    rewrite IHt1, shift_e2t. reflexivity.
  -
    rewrite IHt1_1, IHt1_2; auto.
  -
    rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  -
    rewrite IHt1_1, IHt1_2.
    rewrite shift_sub_lt. reflexivity.
    compute. apply le_n_S. apply le_0_n.
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


Theorem T11_3_1_1_1 : forall t' t'',
  t' -->e t'' ->
  (e2t t') -->i (e2t t'').
Proof.
  induction t'; intros; simpl; try solve_by_inverts 2.
  -
    inversion H; subst; simpl; try solve [constructor; auto].
    +
      apply IHt'2 in H4. apply Ei_App2; auto. destruct t'1; simpl; try constructor; solve_by_invert; auto.
    +
      rewrite subst_e2t; auto.
      constructor.
      destruct t'2; try constructor; solve_by_invert.
  -
    inversion H; subst; simpl; try constructor; auto.
  -
    inversion H; subst; simpl; try constructor; auto; try solve_by_invert.
    +
      constructor.
    +
      erewrite <- sub_shift. constructor. destruct t'1; try solve_by_invert; constructor.
Qed.    


Theorem T11_3_1_1_2 : forall t u,
  (e2t t) -->i u ->
  exists t', u = e2t t' /\ t -->e t'.
Proof.
  induction t; simpl; intros; try solve_by_invert.
  -
    inversion H; subst; simpl; try constructor.
    +
      apply IHt1 in H3; destruct H3; destruct H0; subst. exists (app x t2); split; try constructor; auto.
    +
      apply IHt2 in H4; destruct H4; destruct H0; subst. exists (app t1 x); split; try constructor; auto.
      destruct t1; try solve_by_invert; constructor.
    +
      destruct t1; try solve_by_invert. simpl in H0. inversion H0; subst.
      exists (subst 0 t2 t1). split. symmetry. apply subst_e2t.
      constructor.
      destruct t2; try solve_by_invert; constructor.
  -
    inversion H; subst.
    +
      destruct t1; try solve_by_invert. simpl in H1. exists t2. split; auto; constructor.
    +
      destruct t1; try solve_by_invert. simpl in H1. exists t3; split; auto; constructor.
    +
      apply IHt1 in H4. destruct H4; destruct H0; subst.
      exists (If x t2 t3); split; try constructor; auto.
  -
    inversion H; subst.
    +
      subst. inversion H3.
    +
      apply IHt1 in H4. destruct H4; destruct H0; subst. exists (seq x t2); split; try constructor; auto.
    +
      exists t2. split; try constructor; auto. apply sub_shift. destruct t1; try solve_by_invert; constructor.
Qed.

Reserved Notation "ctx '|-' t '\in' T" (at level 40).
Inductive has_type : context -> term -> ty -> Prop :=
| T_True: forall ctx,
      ctx |- tru \in Bool
| T_False: forall ctx,
      ctx |- fls \in Bool
| T_If: forall ctx t1 t2 t3 T',
      ctx |- t1 \in Bool ->
      ctx |- t2 \in T' ->
      ctx |- t3 \in T' ->
      ctx |- (If t1 t2 t3) \in T'
| T_Var: forall ctx n1 t,
      getbinding n1 ctx = Some t ->
      ctx |- (var n1) \in t
| T_Abs: forall ctx x T1 t2 T2,
      ((x, T1) :: ctx) |- t2 \in T2 ->
      ctx |- (abs x T1 t2) \in (T1 |--> T2)
| T_App: forall ctx t1 T11 T12 t2,
      ctx |- t1 \in (T11 |--> T12) ->
      ctx |- t2 \in T11 ->
      ctx |- app t1 t2 \in T12
| T_Unit: forall ctx,
    ctx |- unit \in Unit
| T_Seq : forall ctx t1 t2 T2,
    ctx |- t1 \in Unit ->
    ctx |- t2 \in T2 ->
    ctx |- (seq t1 t2) \in T2

where " ctx '|-' x '\in' t " := (has_type ctx x t).

Lemma appGetbind : forall ctx ctx' n,
    getbinding (n + (length ctx)) (ctx ++ ctx') = getbinding n ctx'.
Proof.
  induction ctx; simpl; intros; auto.
  rewrite <- plus_n_O; reflexivity.
  rewrite Nat.add_succ_r. simpl. apply IHctx.
Qed.

Lemma length1_Some : forall n ctx ctx1 ctx2 T,
    n < length ctx ->
    getbinding n (ctx ++ ctx1) = Some T ->
    getbinding n (ctx ++ ctx2) = Some T.
Proof.
  induction n; simpl; intros. destruct ctx. inversion H. simpl. simpl in H0. apply H0.
  destruct ctx. inversion H. simpl. destruct ( (p :: ctx) ++ ctx1) eqn:IHH. inversion H0. inversion IHH; subst.
  eapply IHn in H0. apply H0. simpl in H. apply Lt.lt_S_n in H. apply H.
Qed.

Theorem T11_3_1_2 : forall t1 T ctx,
    ctx |- t1 \in T <->
    ctx |- (e2t t1) \in T.
Proof.
  split; generalize dependent T; generalize dependent ctx.
  -
    induction t1; simpl; intros; auto; inversion H; subst; try solve [econstructor; eauto].
    +
      econstructor; eauto. constructor; auto.
      admit.
  -
    induction t1; simpl; intros; auto; inversion H; subst; try solve [econstructor; eauto].
    inversion H3; subst.
    constructor; eauto.
    admit.
Abort.

End E11_1.

End deBruijin.
