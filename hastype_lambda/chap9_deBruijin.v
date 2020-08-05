Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
From Coq Require Import Lists.List.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Import ListNotations.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Inductive ty : Type :=
| Bool
|Arrow (ty1 ty2: ty).
Notation "t1 '|-->' t2" := (Arrow t1 t2) (at level 40).

Inductive term : Type :=
(*純粋λ計算*)
| Var (n1 n2: nat)
| Abs (name: string) (typ: ty) (t: term)
| App (t1 t2: term)
(*ぶーる*)
| Tru
| Fls
| If (t1 t2 t3: term).

Inductive bind : Type :=
|VarBind (t: ty).


Definition context : Type :=
  list (string * bind).

Definition ctxlen (ctx: context) :=
  length ctx.

Definition eqb_string s1 s2:=
  String.eqb s1 s2.

Definition addbind (ctx: context) x bind :=
  (x, bind) :: ctx.


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

Definition getTtypeFromCtx ctx i:=
  match getbinding ctx i with
  | Some (VarBind t) => Some t
  | None => None
  end.


Definition isval t:=
match t with
| Tru => true
| Fls => true
| Abs _ _ _ => true
| _ => false
end.

Inductive N : Type :=
| P (n: nat)
| M1.

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

Fixpoint shift_walk c d t :=
  match t with
  | Var x n =>
    if leb c x then
      match d with
      | M1 =>
        Var (x - 1) (n - 1)
      | P d' =>
        Var (x + d') (n + d')
      end
    else
      match d with
      | M1 =>
        Var x (n - 1)
      | P d' =>
        Var x (n + d')
      end
  | Abs t x t1 =>
    Abs t x (shift_walk (S c) d t1)
  | App t1 t2 =>
    App (shift_walk c d t1) (shift_walk c d t2)
  | If t1 t2 t3 =>
    If (shift_walk c d t1) (shift_walk c d t2) (shift_walk c d t3)
  | _ => t
  end.

Definition shift d t := shift_walk 0 d t.

Fixpoint sub_walk j s c t :=
  match t with
  | Var x n =>
    let jc :=
        match c with
        | M1 => (j - 1)
        | P c' => (j + c')
        end
    in
    if eqb_nat x (jc) then
      shift c s
    else
      Var x n
  | Abs t x t1 =>
    let sc :=
        match c with
        | M1 => P 0
        | P c' => P (c' + 1)
        end
    in
    Abs t x (sub_walk j s sc t1)
  | App t1 t2 =>
    App (sub_walk j s c t1) (sub_walk j s c t2)
  | If t1 t2 t3 =>
    If (sub_walk j s c t1) (sub_walk j s c t2) (sub_walk j s c t3)
  | _ => t
  end.

Definition sub j s t :=
  sub_walk j s (P 0) t.

Definition subtop s t :=
  shift (M1) (sub 0 (shift (P 1) s) t).

Inductive value : term -> Prop :=
| V_tru : value Tru
| V_fls : value Fls
| V_abs :forall typ name t1, value (Abs typ name t1).


Reserved Notation " t '-->' t' " (at level 40).
Inductive step :term -> term -> Prop :=
| E_IfTrue : forall t2 t3,
    If Tru t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If Fls t2 t3 --> t3
| E_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3
| E_App1 : forall t1 t2 t1',
    t1 --> t1' ->
    App t1 t2 --> App t1' t2
| E_App2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    App v1 t2 --> App v1 t2'
| E_AppAbs : forall typ str t12 t2,
    value t2 ->
    App (Abs typ str t12) t2 --> subtop t2 t12

  where " t '-->' t' " := (step t t').

Fixpoint eqb_ty (T1 T2: ty) : bool :=
  match (T1, T2) with
  | (Bool, Bool) => true
  | (T11 |--> T12, T21 |--> T22) =>
    andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _ => false
  end.

Fixpoint inb (ctx: context) (name: string) (T: ty): bool :=
  match ctx with
    | [] => false
    | (n1, VarBind b) :: m =>
      if andb (eqb_string name n1) (eqb_ty T b) then
        true
      else inb m name T
  end.

Reserved Notation "ctx '|-' x '\in' t" (at level 40).
Inductive has_type : context -> term -> ty -> Prop :=
| T_True:
    forall ctx,
      ctx |- Tru \in Bool
| T_False:
    forall ctx,
      ctx |- Fls \in Bool
| T_If:
    forall ctx t1 t2 t3 T',
      ctx |- t1 \in Bool ->
      ctx |- t2 \in T' ->
      ctx |- t3 \in T' ->
      ctx |- (If t1 t2 t3) \in T'
| T_Var:
    forall ctx n1 n2 t,
      getTtypeFromCtx n1 ctx = Some t ->
      ctx |- (Var n1 n2) \in t
| T_Abs:
    forall ctx x T1 t2 T2,
      (addbind ctx x (VarBind T1)) |- t2 \in T2 ->
      ctx |- (Abs x T1 t2) \in (T1 |--> T2)
| T_App:
    forall ctx t1 T11 T12 t2,
      ctx |- t1 \in (T11 |--> T12) ->
      ctx |- t2 \in T11 ->
      ctx |- App t1 t2 \in T12

where " ctx '|-' x '\in' t " := (has_type ctx x t).


Example type1:
  [("f"%string, VarBind (Bool |--> Bool))] |- App (Var 0 1) (If Fls Tru Fls) \in Bool.
Proof.
  eapply T_App. apply T_Var. reflexivity.
  apply T_If. apply T_False. apply T_True. apply T_False.
Qed.

Example type2:
  [("f"%string, VarBind (Bool |--> Bool))] |- (Abs "x" Bool (App (Var 1 2) (If (Var 0 1) Fls (Var 0 1)))) \in (Bool |--> Bool).
Proof.
  apply T_Abs. eapply T_App. apply T_Var. reflexivity.
  apply T_If. apply T_Var. reflexivity. apply T_False. apply T_Var. reflexivity.
Qed.

Lemma eqb_ty_eq : forall T1 T2,
    eqb_ty T1 T2 = true <-> T1 = T2.
Proof.
  split; intros.
  generalize dependent T2; induction T1; intros.
  destruct T2; auto. inversion H.
  inversion H. destruct T2. inversion H1. apply andb_prop in H1.
  inversion H1. apply IHT1_1 in H0. apply IHT1_2 in H2. rewrite H0, H2. reflexivity.

  generalize dependent T2; induction T1; intros.
  destruct T2. reflexivity. inversion H.

  destruct T2; auto. inversion H.
  simpl. inversion H. rewrite <- H1. rewrite <- H2. apply andb_true_intro.
  split; auto.
Qed.


Lemma E9_3_2 :  forall n T,
    not (exists ctx,ctx |- App (Var (n) (n + 1)) (Var (n) (n + 1)) \in T).
Proof.
  intros; intro. inversion H.
  inversion H0; subst. inversion H4. inversion H6; subst.
  rewrite H12 in H7. inversion H7. apply eqb_ty_eq in H2.
  generalize H2. clear. generalize dependent T.
  induction T11; intros. inversion H2. inversion H2. apply andb_prop in H0. inversion H0.
  apply IHT11_1 in H. apply H.
Qed.

Lemma T9_3_3 : forall t1 ctx T1 T2,
    ctx |- t1 \in T1 ->
    ctx |- t1 \in T2 ->
    T1 = T2.
Proof.
  induction t1; intros.
  -
    inversion H; inversion H0; subst. rewrite H5 in H10. inversion H10; auto.
  -
    inversion H; inversion H0; subst.
    apply eqb_ty_eq. simpl; apply andb_true_intro; split; auto.
    clear. induction typ; auto. simpl. apply andb_true_intro. split; auto.
    apply eqb_ty_eq. apply (IHt1 (addbind ctx name (VarBind typ)) T3 T5); auto.
  -
    inversion H; inversion H0; subst.
    apply IHt1_1 with (T2:= (T0 |--> T2)) in H4; auto.
    inversion H4; reflexivity.
  -
    inversion H; inversion H0; subst; auto.
  -
    inversion H; inversion H0; subst; auto.
  -
    inversion H; inversion H0; subst; auto.
    apply (IHt1_2 ctx T1 T2); auto.
Qed.

Lemma L9_3_4_bool : forall ctx v,
    value v ->
    ctx |- v \in Bool ->
    v = Tru \/ v = Fls.
Proof.
  intros. inversion H0; subst. left; auto. right; auto.
  inversion H. inversion H. inversion H.
Qed.

Lemma L9_3_4_Abs: forall ctx v T1 T2,
    value v ->
    ctx |- v \in (T1 |--> T2) ->
    exists x t, v = Abs x T1 t.
Proof.
  intros. inversion H0; subst; try solve_by_invert.
  exists x, t2. reflexivity.
Qed.

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

Fixpoint fv_card (t: term) (n dep: nat) :=
  match t with
  | Var n1 n2 =>
    match dep with
    | 0 => 1
    | _ =>
      if leb n n1 then 1 else 0
    end
  | Abs x T t1 =>
    fv_card (t1) (n + 1) (dep + 1)
  | App t1 t2 =>
    (fv_card t1 n dep) + (fv_card t2 n (dep + 1))
  | Tru => 0
  | Fls => 0
  | If t1 t2 t3 =>
    (fv_card t1 n dep) + (fv_card t2 n dep) + (fv_card t3 n dep)
  end.

Lemma le_leb : forall n1 n2,
    leb n1 n2 = true -> n1 <= n2.
Proof.
  destruct n1; intros.
  apply le_0_n.
  induction n2. inversion H. inversion H.
  destruct (eqb_nat n1 n2) eqn: IH1. apply eqb_eq in IH1. rewrite IH1; auto.
  apply IHn2 in H1. apply le_S. apply H1.
Qed.


Lemma fv_card_succ1 : forall t n1 n2,
    fv_card t (n1 +1) n2 <= fv_card t n1 n2.
Proof.
  induction t; intros; simpl; auto.
  -
    destruct n3; auto. destruct (leb n0 n1) eqn:IH1; destruct (leb (n0 + 1) n1) eqn:IH2; auto.
    apply le_leb in IH2. rewrite PeanoNat.Nat.add_1_r in IH2. apply Le.le_Sn_le in IH2. apply leb_le in IH2.
    rewrite IH1 in IH2. inversion IH2.
  -
    apply PeanoNat.Nat.add_le_mono; auto.
  -
    apply PeanoNat.Nat.add_le_mono; auto.
    apply PeanoNat.Nat.add_le_mono; auto.
Qed.

Lemma le_trance : forall n1 n2 n3,
    n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  intros. generalize dependent n3. induction H; intros; auto.
  destruct H0. apply IHle. apply le_S. apply le_n.
  apply IHle. apply le_S. apply le_S_n. apply le_S. apply H0.
Qed.

Lemma fv_card_succ2 : forall t n1 n2,
    fv_card t n1 (S n2) <= fv_card t n1 n2.
Proof.
  induction t; intros; simpl; auto.
  -
    destruct (leb n0 n1); destruct n3; auto.
  -
    apply PeanoNat.Nat.add_le_mono; auto.
  -
    apply PeanoNat.Nat.add_le_mono; auto.
    apply PeanoNat.Nat.add_le_mono; auto.
Qed.

Theorem T9_3_5 : forall t T ctx,
    fv_card t 0 0 = 0 ->
    ctx |- t \in T ->
    value t \/ exists t', t --> t'.
Proof.
  induction t; intros.
  -
    inversion H.
  -
    left. apply V_abs.
  -
    right.
    simpl in H. apply Plus.plus_is_O in H. destruct H.
    inversion H0; subst. apply IHt1 in H5; auto. apply IHt2 in H7; auto.
    destruct H5. destruct H7.
    inversion H0; subst. inversion H2; subst; try solve_by_invert.
    exists (subtop t2 t0). apply E_AppAbs. apply H3.
    inversion H3. exists (App t1 x). apply E_App2; auto.
    inversion H2. exists (App x t2). apply E_App1; auto.
    admit.
  -
    left; apply V_tru.
  -
    left; apply V_fls.
  -
    right.
    simpl in H. apply Plus.plus_is_O in H. destruct H. apply Plus.plus_is_O in H. destruct H.
    inversion H0; subst.
    generalize H7; intros. apply IHt1 in H7; auto.
    inversion H7. apply (L9_3_4_bool ctx t1) in H4.
    destruct H4; rewrite H4. exists t2; apply E_IfTrue.
    exists t3; apply E_IfFalse. apply H3.
    inversion H4. exists (If x t2 t3).
    apply E_If; auto.
Abort.


Theorem T9_3_5 : forall t T,
    [] |- t \in T ->
    value t \/ exists t', t --> t'.
Proof.
  induction t; simpl; intros.
  -
    inversion H; subst. destruct n1; inversion H4.
  -
    left; apply V_abs.
  -
    right.
    inversion H; subst.
    generalize H3; intro. apply IHt1 in H3. destruct H3.
    apply (L9_3_4_Abs [] t1) in H0; auto. inversion H0. inversion H2.
    apply IHt2 in H5. inversion H5. rewrite H3.
    exists (subtop t2 x0). apply E_AppAbs; auto.
    inversion H4. exists (App t1 x1). apply E_App2; auto.
    inversion H1. exists (App x t2); apply E_App1; auto.
  -
    left. apply V_tru.
  -
    left; apply V_fls.
  -
    inversion H; subst. right. generalize H4; intros; apply IHt1 in H4.
    destruct H4. apply (L9_3_4_bool [] t1) in H1; auto. destruct H1; rewrite H1.
    exists t2; apply E_IfTrue. exists t3; apply E_IfFalse. inversion H1.
    exists (If x t2 t3); apply E_If; auto.
Qed.

Lemma L9_3_8: forall t s x S T ctx,
    addbind ctx x (VarBind S) |- t \in T ->
    ctx |- s \in S ->
    ctx |- subtop s t \in T.
Proof.
Admitted.

Theorem T9_3_9 : forall t t' T ctx,
    ctx |- t \in T ->
    t --> t' ->
    ctx |- t' \in T.
Proof.
  intros. generalize dependent T. induction H0; subst; simpl; intros; auto.
  -
    inversion H; subst. apply H6.
  -
    inversion H; subst. apply H7.
  -
    inversion H; subst. apply IHstep in H5. apply T_If; auto.
  -
    inversion H; subst. apply IHstep in H4. apply T_App with T11; auto.
  -
    inversion H1; subst. apply IHstep in H7. apply T_App with T11; auto.
  -
    inversion H0; subst. clear H0.
    inversion H4; subst. eapply L9_3_8. apply H2. apply H6.
Qed.

