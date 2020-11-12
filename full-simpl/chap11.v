Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
From Coq Require Import Lists.List.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Import ListNotations.
Load "../std".

Module deBruijin.

Module E11_1.

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

Fixpoint shift (d k : nat) (t : term) : term :=
match t with
| var x => var (if leb d x then x + k else x)
| abs x T t' => abs x T (shift (S d) k t')
| app t1 t2 => app (shift d k t1) (shift d k t2)
| tru => tru
| fls => fls
| If t1 t2 t3 =>
  If (shift d k t1) (shift d k t2) (shift d k t3)
| unit => unit
| seq t1 t2 =>
  seq (shift d k t1) (shift d k t2)
end.

Fixpoint subst (d : nat) (s t: term) : term :=
match t with
| var x =>
  if eqb_nat d x then s
  else if ltb d x then var (pred x) else var x
| abs x T t' => abs x T (subst (S d) (shift 0 1 s) t')
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
  destruct eqb_nat eqn:IH1. apply eqb_eq in IH1. rewrite IH1 in IHn. rewrite leb_refl in IHn; inversion IHn.
  apply leb_F in IHn. apply Nat.nle_gt in IHn. apply Nat.lt_lt_succ_r in IHn. apply lt_not_le in IHn.
  apply leb_F in IHn. rewrite IHn; reflexivity.
Qed.

Lemma shift_sub : forall t1 t2 n m,
    subst n t2 (shift n (S m) t1) = shift n m t1.
Proof.
  induction t1; intros; simpl; auto.
  destruct leb eqn:IH1; destruct eqb_nat eqn:IH2; try apply eqb_eq in IH2; subst.
  rewrite leb_S_l in IH1. inversion IH1.
  apply le_leb in IH1. eapply le_plus_trans with (p:= (S m)) in IH1. apply leb_le in IH1. apply leb_neq_lt in IH1; auto. rewrite IH1. rewrite Nat.add_succ_r. simpl. reflexivity.
  rewrite leb_refl in IH1; inversion IH1.
  destruct ltb eqn:IH3. apply ltb_to_leb in IH3. rewrite IH3 in IH1; inversion IH1.
  reflexivity.
  rewrite IHt1. reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
Qed.

Lemma shift_0_t : forall t n,
    shift n 0 t = t.
Proof.
  induction t; simpl; intros; auto.
  rewrite <- plus_n_O. destruct leb; reflexivity.
  rewrite IHt; reflexivity.
  rewrite IHt1, IHt2; reflexivity.
  rewrite IHt1, IHt2, IHt3; reflexivity.
  rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma shift_sub_1 : forall t1 t2 n,
    subst n t2 (shift n 1 t1) = t1.
Proof.
  intros. rewrite shift_sub. rewrite shift_0_t. reflexivity.
Qed.

Fixpoint e t :=
  match t with
  | var x => var x
  | abs x T t' => abs x T (e t')
  | app t1 t2 => app (e t1) (e t2)
  | If t1 t2 t3 => If (e t1) (e t2) (e t3)
  | seq t1 t2 => app (abs "x" Unit (shift 0 1 (e t2))) (e t1)
  | _ => t
  end.

Lemma shift_shift : forall t n d1 d2,
    shift n d1 (shift n d2 t) = shift n (d2 + d1) t.
Proof.
  induction t; simpl; intros; auto.
  -
    destruct (leb n0 n) eqn:IH1.
    apply le_leb in IH1. eapply le_plus_trans with (p:= d2) in IH1.
    apply leb_le in IH1. rewrite IH1. rewrite Nat.add_assoc. reflexivity.
    rewrite IH1. reflexivity.
  -
    rewrite IHt. reflexivity.
  -
    rewrite IHt1, IHt2. reflexivity.
  -
    rewrite IHt1, IHt2, IHt3; reflexivity.
  -
    rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma leb_S_n_S : forall n m,
    leb n m = leb (S n) (S m).
Proof.
  intros. destruct leb eqn:IH.
  apply le_leb in IH. apply le_n_S in IH. apply leb_le in IH.
  rewrite IH. reflexivity.
  apply leb_F in IH. apply Nat.nle_gt in IH. apply lt_n_S in IH.
  apply Nat.nle_gt in IH. apply leb_F in IH. rewrite IH; reflexivity.
Qed.


Notation "t1 ';' t2" := (seq t1 t2) (at level 50).
Notation "'[' n ':=' t2 ']' t1" := (subst n t2 t1) (at level 100).

Fixpoint e2t n t :=
  match t with
  | var x => var x
  | abs x T t' => abs x T (e2t (S n) t')
  | app t1 t2 => app (e2t n t1) (e2t n t2)
  | If t1 t2 t3 => If (e2t n t1) (e2t n t2) (e2t n t3)
  | seq t1 t2 => app (abs "x" Unit (shift n 1 (e2t n t2))) (e2t n t1)
  | _ => t
  end.

Lemma shift_e : forall t n1 n2,
  e2t (S n1) (shift n2 1 t) = shift n2 1 (e2t n1 t) .
Proof.
  induction t; simpl; intros; auto.
  rewrite IHt. reflexivity.
  rewrite IHt1, IHt2; reflexivity.
  rewrite IHt1, IHt2, IHt3; reflexivity.
  rewrite IHt1, IHt2.
Admitted.

Lemma subst_e2t : forall t1 t2 n,
    e2t n ([n := t2]t1) = ([n := (e2t n t2)](e2t (S n) t1)).
Proof.
  induction t1; simpl; intros; eauto.
  destruct eqb_nat; eauto.
  destruct ltb; auto.
  rewrite IHt1.
  rewrite shift_e. reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2.
Admitted.

Theorem T11_3_1_1_1__ : forall t t',
  t -->e t' ->
  (e2t 0 t) -->i (e2t 0 t').
Proof.
  induction t; intros; simpl; try solve_by_inverts 2.
  -
    inversion H; subst; simpl; try constructor; auto.
    +
      destruct t1; try solve_by_invert; constructor.
    +
      rewrite subst_e2t; auto. constructor.
      destruct t2; try solve_by_invert; constructor.
  -
    inversion H; subst; simpl; try constructor; auto.
  -
    inversion H; subst; simpl; try constructor; auto; try solve_by_invert.
    +
      constructor.
    +
      erewrite <- shift_sub_1.  constructor. destruct t1; try solve_by_invert; constructor.
Qed.

Lemma subst_e : forall t1 t2 n,
    e (subst n t2 t1) = subst n (e t2) (e t1).
Proof.
  induction t1; intros; simpl; auto; try solve_by_invert.
  destruct eqb_nat; auto.
  destruct ltb; auto.
  rewrite IHt1. admit.
  rewrite IHt1_1, IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2.
Admitted.

Theorem T11_3_1_1_1 : forall t t',
  t -->e t' ->
  (e t) -->i (e t').
Proof.
  induction t; intros; simpl; try solve_by_inverts 2.
  -
    inversion H; subst; simpl; try constructor; auto.
    +
      destruct t1; try solve_by_invert; constructor.
    +
      rewrite subst_e; auto. constructor; destruct t2; try solve_by_invert; constructor.
  -
    inversion H; subst; simpl; try constructor; auto.
  -
    inversion H; subst; simpl; try constructor; auto; try solve_by_invert.
    +
      constructor.
    +
      erewrite <- shift_sub_1. constructor. destruct t1; try solve_by_invert; constructor.
Qed.

Theorem T11_3_1_1_2 : forall t u,
  (e t) -->i u ->
  exists t', u = e t' /\ t -->e t'.
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
      exists (subst 0 t2 t1). split. symmetry. apply subst_e.
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
      exists t2. split; try constructor; auto. apply shift_sub_1. destruct t1; try solve_by_invert; constructor.
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
  rewrite <- plus_Snm_nSm. simpl. apply IHctx.
Qed.

Lemma length1_Some : forall n ctx ctx1 ctx2 T,
    n < length ctx ->
    getbinding n (ctx ++ ctx1) = Some T ->
    getbinding n (ctx ++ ctx2) = Some T.
Proof.
  induction n; simpl; intros. destruct ctx. inversion H. simpl. simpl in H0. apply H0.
  destruct ctx. inversion H. simpl. destruct ( (p :: ctx) ++ ctx1) eqn:IHH. inversion H0. inversion IHH; subst.
  eapply IHn in H0. apply H0. simpl in H. apply lt_S_n in H. apply H.
Qed.

Lemma shifting : forall t g g1 g2 T,
  (g1 ++ g) |- t \in T ->
  (g1 ++ g2 ++ g) |- (shift (length g1) (length g2) t) \in T.
Proof.
  induction t; intros; inversion H; subst; clear H; try solve [econstructor; eauto]; simpl.

  apply T_Var. destruct (leb) eqn:IH. apply le_leb in IH.
  generalize dependent g. generalize dependent T. generalize dependent n.
  induction g1; simpl; intros; eauto. unfold getbinding. rewrite appGetbind. apply H2.
  destruct n. inversion IH. simpl.
  apply le_S_n in IH. simpl in H2. eapply IHg1 in IH; eauto.

  apply leb_neq in IH. eapply length1_Some in IH. apply IH. apply H2.

  apply T_Abs.
  assert (S (length g1) = length ((name, typ) :: g1)). reflexivity.
  rewrite H. apply IHt with (g1:= ((name, typ) :: g1)). apply H5.
Qed.

Lemma shifting_l : forall t g g1 g2 T,
  (g1 ++ g2 ++ g) |- (shift (length g1) (length g2) t) \in T ->
  (g1 ++ g) |- t \in T.
Proof.
  induction t; intros; inversion H; subst; clear H; try solve [econstructor; eauto]; simpl.
  -
    apply T_Var. destruct (leb) eqn:IH. apply le_leb in IH.
    generalize dependent g. generalize dependent T. generalize dependent n.
    induction g1; simpl; intros; eauto. unfold getbinding in H2. rewrite appGetbind in H2. apply H2.
    destruct n. inversion IH. simpl.
    apply le_S_n in IH. simpl in H2. eapply IHg1 in IH; eauto.
    apply leb_neq in IH. eapply length1_Some in IH. apply IH. apply H2.
  -
    apply T_Abs.
    assert (S (length g1) = length ((name, typ) :: g1)). reflexivity. rewrite H in H5.
    eapply IHt with (g1:= ((name, typ) :: g1)). apply H5.
Qed.

Theorem T11_3_1_2 : forall t T ctx n,
    ctx |- t \in T <->
    ctx |- (e2t n t) \in T.
Proof.
  split; generalize dependent T; generalize dependent ctx; generalize dependent n.
  -
    induction t; simpl; intros; auto; inversion H; subst; try solve [econstructor; eauto].
    +
      econstructor; eauto. constructor; auto.
      admit.
  -
    induction t; simpl; intros; auto; inversion H; subst; try solve [econstructor; eauto].
    inversion H3; subst.
    constructor; eauto. eapply IHt2.
    admit.
Abort.

(*
Theorem T11_3_1_2 : forall t T ctx,
    ctx |- t \in T <->
    ctx |- (e2t t) \in T.
Proof.
  split; generalize dependent T; generalize dependent ctx.
  -
    induction t; simpl; intros; auto; inversion H; subst; try solve [econstructor; eauto].
    +
      econstructor. constructor; auto.
      assert (("x"%string, Unit) :: ctx = [] ++ [("x"%string, Unit)] ++ ctx). reflexivity. rewrite H0.
      apply shifting. simpl. apply IHt2. apply H5.
      apply IHt1. apply H3.
  -
    induction t; simpl; intros; inversion H; subst; try solve [econstructor; eauto].
    inversion H3; subst. apply T_Seq. apply IHt1. apply H5. apply IHt2.
    assert (ctx = [] ++ ctx). reflexivity. rewrite H0.
    eapply shifting_l with (g2:= [("x"%string, Unit)]).
    assert ([] ++ [("x"%string, Unit)] ++ ctx = [("x"%string, Unit)] ++ ctx). reflexivity.
    apply H2.
Qed.
*)
End E11_1.

End deBruijin.

Module string.

Module Seq.
Inductive ty : Type :=
| Bool
| Unit
|Arrow (ty1 ty2: ty) .
Notation "t1 '|-->' t2" := (Arrow t1 t2) (at level 40).

Inductive term : Type :=
(*純粋λ計算*)
| var (name: string)
| abs (name: string) (typ: ty) (t: term)
| app (t1 t2: term)
(*ぶーる*)
| tru
| fls
| unit
| If (t1 t2 t3: term)
| seq (t1 t2: term).

Inductive value : term -> Prop :=
  | v_abs : forall x T t, value (abs x T t)
  | v_tru : value tru
  | v_fls : value fls
  | v_uni : value unit.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | var x' => if String.eqb x x' then s else t
  | abs x' T t1 => abs x' T (if String.eqb x x' then t1 else ([x:=s] t1))
  | app t1 t2 => app ([x:=s] t1) ([x:=s] t2)
  | tru => tru
  | fls => fls
  | unit => unit
  | If t1 t2 t3 => If ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | seq t1 t2 => seq ([x:=s]t1) ([x:=s]t2)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : term -> term -> Prop :=
  | E_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | E_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | E_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1 t2'
  | E_IfTru : forall t1 t2,
      (If tru t1 t2) --> t1
  | E_IfFls : forall t1 t2,
      (If fls t1 t2) --> t2
  | E_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (If t1 t2 t3) --> (If t1' t2 t3)
  | E_seq : forall t1 t1' t2,
      t1 --> t1' ->
      seq t1 t2 --> seq t1' t2
  | E_SeqNext : forall v1 t2,
      value v1 ->
      seq v1 t2 --> t2

where "t1 '-->' t2" := (step t1 t2).


Definition context := partial_map ty.

Inductive appears_free_in : string -> term -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (If t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (If t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (If t1 t2 t3)
  | afi_seq1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (seq t1 t2)
  | afi_seq2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (seq t1 t2).

Notation "x '∈fv' t" := (appears_free_in x t) (at level 50).

Fixpoint free x t :=
  match t with
  | var x' => eqb x x'
  | app t1 t2 =>
    orb (free x t1) (free x t2)
  | abs y T t1 =>
    if eqb x y then false
    else free x t1
  | If t1 t2 t3 =>
    (free x t1) || (free x t2) || (free x t3)
  | tru => false
  | fls => false
  | unit => false
  | seq t1 t2 =>
    (free x t1) || (free x t2)
  end.

Fixpoint e x t :=
  match t with
  | abs s T t' => abs s T (e x t')
  | app t1 t2 => app (e x t1) (e x t2)
  | If t1 t2 t3 => If (e x t1) (e x t2) (e x t3)
  | seq t1 t2 => app (abs x Unit (e x t2)) (e x t1)
  | _ => t
  end.

Open Scope string.
Lemma subst_e_free : forall t1 t2 x,
    not (x ∈fv t1) ->
    [x := t2]t1 = t1.
Proof.
  induction t1; simpl; intros; auto;
    try (rewrite IHt1_1, IHt1_2; try rewrite IHt1_3; auto; intro; apply H; solve [constructor; auto]).
  -
    destruct eqb eqn:IH; auto. apply String.eqb_eq in IH; subst.
    induction H. constructor.
  -
    destruct eqb eqn:IH; auto. rewrite IHt1; auto.
    intro. apply H. constructor. intro. subst. rewrite String.eqb_refl in IH.
    inversion IH. apply H0.
Qed.


Lemma afi_e : forall t x,
    x ∈fv e x t -> x ∈fv t.
Proof.
  induction t; simpl; intros; auto.
  inversion H; subst. constructor; auto.
  inversion H; subst; solve [constructor; auto].
  inversion H; subst; solve [constructor; auto].
  inversion H; subst; try solve [constructor; auto].
  inversion H2; subst. solve [constructor; auto].
Qed.


Lemma subst_e : forall t1 t2 x x',
    not (x' ∈fv t1) ->
    e x ([x':= t2]t1) = [x' := e x t2](e x t1).
Proof.
  induction t1; simpl; intros; auto.
  destruct eqb; auto.
  destruct eqb eqn:IH. apply String.eqb_eq in IH; subst; auto.
  rewrite IHt1; auto.
  intro. apply H. constructor. intro; subst. rewrite String.eqb_refl in IH. inversion IH. apply H0.
  rewrite IHt1_1, IHt1_2; auto; intro; apply H; solve [constructor; auto].
  rewrite IHt1_1, IHt1_2, IHt1_3; auto; intro; apply H; solve [constructor; auto].
  rewrite IHt1_1, IHt1_2; auto. destruct eqb eqn:IH; auto. apply String.eqb_eq in IH; subst.
  rewrite subst_e_free. reflexivity.
  intro. apply H. apply afi_seq2. apply afi_e. apply H0.
  intro. apply H; solve [constructor; auto].
  intro. apply H; solve [constructor; auto].
Qed.

Theorem T11_3_1_1 : forall t t' x,
  t --> t' ->
  not (x ∈fv t) -> not (x ∈fv t') ->
  e x t --> e x t'.
Proof.
  induction t; simpl; intros; try solve_by_invert.
  -
    inversion H; subst.
    +
      rewrite subst_e. constructor; auto. destruct t2; try solve_by_invert; constructor.
      admit.
    +
      constructor. apply IHt1; auto.
      intro; apply H0; constructor; auto.
      intro; apply H1; constructor; auto.
    +
      constructor; auto. destruct t1; try solve_by_invert; constructor.
      apply IHt2; auto; intro.
      apply H0; solve[constructor; auto].
      apply H1; solve[constructor; auto].
  -
    inversion H; subst; simpl; try constructor; auto.
    apply IHt1; auto; intro. apply H0; constructor; auto.
    apply H1; solve[constructor; auto].
  -
    inversion H; subst; simpl.
    +
      constructor; auto. destruct t2; try solve_by_invert; constructor.
      apply IHt1; auto; intro.
      apply H0; constructor; auto.
      apply H1; constructor; auto.
Admitted.


Reserved Notation "ctx '|-' t '\in' T" (at level 40).
Inductive has_type : context -> term -> ty -> Prop :=
  | T_Var : forall ctx x T,
      ctx x = Some T ->
      ctx |- var x \in T
  | T_Abs : forall ctx x T11 T12 t12,
      (x |-> T11 ; ctx) |- t12 \in T12 ->
      ctx |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T11 T12 ctx t1 t2,
      ctx |- t1 \in Arrow T11 T12 ->
      ctx |- t2 \in T11 ->
      ctx |- app t1 t2 \in T12
  | T_Tru : forall ctx,
       ctx |- tru \in Bool
  | T_Fls : forall ctx,
       ctx |- fls \in Bool
  | T_If : forall t1 t2 t3 T ctx,
       ctx |- t1 \in Bool ->
       ctx |- t2 \in T ->
       ctx |- t3 \in T ->
       ctx |- If t1 t2 t3 \in T

where "ctx '|-' t '\in' T" := (has_type ctx t T).

End Seq.

End string.
