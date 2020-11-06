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

Fixpoint shift (c : nat) (t : term) : term :=
match t with
| var x => var (if leb c x then (S x) else x)
| abs x T t' => abs x T (shift (S c) t')
| app t1 t2 => app (shift c t1) (shift c t2)
| tru => tru
| fls => fls
| If t1 t2 t3 => If (shift c t1) (shift c t2) (shift c t3)
| unit => unit
| seq t1 t2 => seq (shift c t1) (shift c t2)
end.

Fixpoint unshift (c : nat) (t : term) : term :=
match t with
| var x => var (if leb c x then (pred x) else x)
| abs x T t' => abs x T (unshift (S c) t')
| app t1 t2 => app (unshift c t1) (unshift c t2)
| tru => tru
| fls => fls
| If t1 t2 t3 => If (unshift c t1) (unshift c t2) (unshift c t3)
| unit => unit
| seq t1 t2 => seq (unshift c t1) (unshift c t2)
end.

Fixpoint subst (d : nat) (s t: term) : term :=
match t with
| var x =>
  if eqb_nat d x then s
  else t
| abs x T t' => abs x T (subst (S d) s t')
| app t1 t2 => app (subst d s t1) (subst d s t2)
| If t1 t2 t3 =>
  If (subst d s t1) (subst d s t2) (subst d s t3)
| seq t1 t2 =>
  seq (subst d s t1) (subst d s t2)
| _ => t
end.

Fixpoint shift_S (d k : nat) (t : term) : term :=
match t with
| var x => var (if leb d x then x + k else x)
| abs x T t' => abs x T (shift_S (S d) k t')
| app t1 t2 => app (shift_S d k t1) (shift_S d k t2)
| tru => tru
| fls => fls
| If t1 t2 t3 =>
  If (shift_S d k t1) (shift_S d k t2) (shift_S d k t3)
| unit => unit
| seq t1 t2 =>
  seq (shift_S d k t1) (shift_S d k t2)
end.

Lemma PM_shift : forall t n,
    unshift n (shift n t) = t.
Proof.
  induction t; simpl; intros; auto.
  -
    destruct (leb n0 n) eqn:IH1.
    apply le_leb in IH1. apply le_S in IH1. apply leb_le in IH1. rewrite IH1. simpl. reflexivity.
    rewrite IH1. reflexivity.
  -
    rewrite IHt. reflexivity.
  -
    rewrite IHt1, IHt2; reflexivity.
  -
    rewrite IHt1, IHt2, IHt3; reflexivity.
  -
    rewrite IHt1, IHt2; reflexivity.
Qed.

Fixpoint subst_s (d : nat) (s t: term) : term :=
match t with
| var x =>
  if eqb_nat d x then
    s
  else
    if ltb d x then
      var (pred x) else var x
| abs x T t' => abs x T (subst_s (S d) s t')
| app t1 t2 => app (subst_s d s t1) (subst_s d s t2)
| tru => tru
| fls => fls
| unit => unit
| If t1 t2 t3 =>
  If (subst_s d s t1) (subst_s d s t2) (subst_s d s t3)
| seq t1 t2 =>
  seq (subst_s d s t1) (subst_s d s t2)
end.

Lemma sub_S : forall t1 t2 n,
unshift n (subst n (shift n t2) t1) = subst_s n t2 t1.
Proof.
  induction t1; simpl; intros; auto.
  destruct eqb_nat eqn:H. rewrite PM_shift. reflexivity.
  simpl. destruct ltb eqn:IH1. apply ltb_to_leb in IH1. rewrite IH1. reflexivity.
  destruct leb eqn:IH2. apply leb_neq_lt in IH2; auto. rewrite IH1 in IH2. inversion IH2.
  reflexivity.

  rewrite <- IHt1. admit.
  rewrite IHt1_1, IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
Abort.


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
    app (abs str typ t12) t2 -->i unshift 0 (subst 0 (shift 0 t2) t12)

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
    app (abs str typ t12) t2 -->e unshift 0 (subst 0 (shift 0 t2) t12)
| E_seq : forall t1 t1' t2,
    t1 -->e t1' ->
    seq t1 t2 -->e seq t1' t2
| E_SeqNext : forall v1 t2,
    value v1 ->
    seq v1 t2 -->e t2
where " t '-->e' t' " := (external_step t t').


Lemma shift_sub : forall t1 t2 n,
unshift n (subst n (shift n t2) (shift n t1)) = t1.
Proof.
  induction t1; intros; simpl; auto.
  destruct leb eqn:IH1. destruct eqb_nat eqn:IH2. apply eqb_eq in IH2. subst.
  generalize Nat.nle_succ_diag_l. intros. apply le_leb in IH1. specialize (H n). induction H. apply IH1.
  simpl. rewrite IH2. rewrite IH1. reflexivity.
  destruct eqb_nat eqn:IH2. apply eqb_eq in IH2. subst. rewrite leb_refl in IH1. inversion IH1.
  simpl. rewrite IH1. reflexivity.
  (* rewrite IHt1. reflexivity. *)
  admit.
  rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2. reflexivity.
Abort.

Fixpoint e2t t :=
  match t with
  | var x => var x
  | abs x T t' => abs x T (e2t t')
  | app t1 t2 => app (e2t t1) (e2t t2)
  | If t1 t2 t3 => If (e2t t1) (e2t t2) (e2t t3)
  | seq t1 t2 => app (abs "x" Unit (shift 0 (e2t t2))) (e2t t1)
  | _ => t
  end.

Lemma shift_sub_1 : forall t1 t2 n,
    unshift n (subst n (shift 0 t2) (shift n t1)) = t1.
Proof.
  induction t1; simpl; intros; auto.
  destruct (leb n0 n) eqn:IH1.
  destruct eqb_nat eqn:IH2. apply eqb_eq in IH2. subst.
  generalize Nat.nle_succ_diag_l; intros. specialize (H n). apply leb_F in H.
  rewrite H in IH1; inversion IH1.
  simpl. rewrite IH2. rewrite IH1. reflexivity.
  destruct eqb_nat eqn:IH2. apply eqb_eq in IH2; subst.
  rewrite leb_refl in IH1; inversion IH1.
  simpl. rewrite IH1. reflexivity.

  rewrite IHt1. reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
Qed.

Lemma subsub : forall t1 t2 n,
    e2t (subst n t2 t1) = subst n (e2t t2) (e2t t1).
Proof.
  induction t1; simpl; intros; auto.

  destruct eqb_nat; auto.
  rewrite IHt1; reflexivity.
  rewrite IHt1_1, IHt1_2; reflexivity.
  rewrite IHt1_1, IHt1_2, IHt1_3; reflexivity.
  rewrite IHt1_1, IHt1_2.



Lemma dekinai : forall t n,
    shift 0 (shift n t) = shift (S n) (shift 0 t).
Proof.
  induction t; simpl; intros; auto.
  repeat rewrite leb0.
  admit.
Abort.

Lemma shift_e2t : forall t n,
    e2t (shift n t) = shift n (e2t t).
Proof.
  induction t; simpl; intros; auto.
  rewrite IHt. reflexivity.
  rewrite IHt1, IHt2; reflexivity.
  rewrite IHt1, IHt2, IHt3; reflexivity.
  rewrite IHt1. rewrite IHt2.
Abort.

Theorem T11_3_1_1_1 : forall t t',
  t -->e t' ->
  (e2t t) -->i (e2t t').
Proof.
  induction t; intros; simpl; try solve_by_inverts 2.
  -
    inversion H; subst; simpl; try constructor; auto.
    +
      destruct t1; try solve_by_invert; constructor.
    +
      admit.
  -
    inversion H; subst; simpl; try constructor; auto.
  -
    inversion H; subst; simpl; try constructor; auto; try solve_by_invert.
    +
      constructor.
    +
      remember (shift 0 (e2t t')) as s.
      rewrite <- (shift_sub_1 (e2t t') (e2t t1) 0).
      subst.
      constructor. destruct t1; try solve_by_invert; constructor.
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
      exists (subst 0 t2 t1). split. symmetry. rewrite sub_e2t.
      constructor. destruct t2; try solve_by_invert; constructor.
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
      exists t2. split; try constructor; auto. apply shift_sub. destruct t1; try solve_by_invert; constructor.
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

Inductive ctx_no : context -> string -> string -> Prop :=
  | ctx_some : forall ctx x T,
      ctx x = Some T ->
      ctx_no ctx x (append x "'")
  | ctx_none : forall ctx x,
      ctx x = None ->
      ctx_no ctx x x.


Lemma ctx_no_det : forall x ctx x' x'',
    ctx_no ctx x x' ->
    ctx_no ctx x x'' ->
    ctx x' = None -> ctx x'' = None ->
    x' = x''.
Proof.
  intros. generalize dependent x''.
  induction H; intros; auto.
  inversion H0; subst. reflexivity.
  rewrite H in H2. inversion H2.
  induction H0; auto.
  rewrite H in H0. inversion H0.
Qed.

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


Inductive free_name : term -> string -> string -> Prop :=
  | free_x : forall x t,
      free x t = true ->
      free_name t x (append x "'")
  | not_free : forall x t,
      free x t = false ->
      free_name t x x.

Lemma name_det : forall x x1 x2 t,
    free_name t x x1 ->
    free_name t x x2 ->
    x1 = x2.
Proof.
  intros. generalize dependent x2; induction H; intros;
  induction H0; auto; rewrite H in H0; inversion H0.
Qed.

Inductive multi_name : term -> string -> string -> Prop :=
| name_refl : forall x t,
    multi_name t x x
| name_malti : forall t x1 x2 x3,
    free_name t x1 x2 ->
    free_name t x2 x3 ->
    multi_name t x1 x3.

Lemma multi_det : forall t x x1 x2,
    multi_name t x x1 -> multi_name t x x2 ->
    free x1 t = false -> free x2 t = false ->
    x1 = x2.
Proof.
  intros. generalize dependent x2. induction H; intros.
  inversion H0; subst; auto.
  admit.
  admit.
Admitted.


Inductive e2t : term -> context -> term -> Prop :=
| evar : forall x ctx, e2t (var x) ctx (var x)
| eabs : forall x T t t' ctx,
    e2t t ctx t' ->
    e2t (abs x T t) ctx (abs x T t')
| eapp : forall t1 t2 t1' t2' ctx,
    e2t t1 ctx t1' -> e2t t2 ctx t2' ->
    e2t (app t1 t2) ctx (app t1' t2')
| etru : forall ctx,
    e2t tru ctx tru
| efls : forall ctx,
    e2t fls ctx fls
| eunit : forall ctx,
    e2t unit ctx unit
| eif : forall ctx t1 t2 t3 t1' t2' t3',
    e2t t1 ctx t1' -> e2t t2 ctx t2' -> e2t t3 ctx t3' ->
    e2t (If t1 t2 t3) ctx (If t1' t2' t3')
| eseq : forall x ctx t1 t2 t1' t2',
    free_name (seq t1 t2) "x" x ->
    e2t t1 ctx t1' -> e2t t2 ctx t2' ->
    e2t (seq t1 t2) ctx (app (abs x Unit t2') t1').

Lemma e2t_det : forall t t1 t2 ctx1 ctx2,
    e2t t ctx1 t1 ->
    e2t t ctx2 t2 ->
    t1 = t2.
Proof.
  induction t; simpl; intros; inversion H; inversion H0; subst; auto .
  erewrite IHt with (t1:= t'); eauto.
  erewrite IHt1 with (t2:= t1'); eauto. erewrite IHt2 with (t1:= t2'); eauto.
  erewrite IHt1 with (t2:= t1'); eauto. erewrite IHt2 with (t1:= t2'); eauto. erewrite IHt3 with (t1:= t3'); eauto.
  erewrite IHt2 with (t1:= t2'); eauto. erewrite IHt1 with (t2:= t1'); eauto.
  erewrite name_det with (x1:= x); eauto.
Qed.

Lemma sub_E : forall t12 t2 n ctx t2' t12',
    e2t t2 ctx t2' -> e2t t12 ctx t12' ->
    e2t (subst n t2 t12) ctx (subst n t2' t12').
Proof.
  induction t12; simpl; intros; inversion H0; subst; simpl; eauto; try solve [inversion H1; subst; auto].
  destruct eqb; auto.
  destruct eqb; eauto. apply eabs; auto.
  apply eapp; auto.
  apply eif; auto.
  destruct eqb; auto.
  admit.

  inversion H0; subst.
  apply eseq; auto.
  destruct (free "x" (seq ([n := t2] t12_1) ([n:= t2] t12_2) )) eqn:IH.

Admitted.

Theorem T11_3_1_1 : forall t t' ctx t1 t1',
  t --> t' ->
  e2t t ctx t1 -> e2t t' ctx t1' ->
  t1 --> t1'.
Proof.
  intros. generalize dependent t1; generalize dependent t1'.
  induction H; intros.

  -
    inversion H0; subst. inversion H4; subst.
    eapply sub_E with (n:= x) in H7; eauto. eapply e2t_det with (t2:= t1') in H7; eauto. subst. apply E_AppAbs.



  induction t; intros; try solve_by_invert.
  -
    inversion H0; subst. inversion H; subst.
    inversion H4; subst. eapply sub_E with (n:= x) in H1; eauto. erewrite e2t_det with (t:= ()). apply E_AppAbs; auto.
    inversion H6; subst; destruct t2'; try solve_by_invert; constructor.

    inversion H1; subst. eapply e2t_det in H7; eauto; subst. apply E_App1; auto.
    eapply IHt1; eauto.

    inversion H1; subst.
    eapply e2t_det in H4; eauto; subst. apply E_App2; auto.
    inversion H5; subst; inversion H6; subst; constructor.
    eapply IHt2; eauto.
  -
    inversion H0; subst. inversion H; subst.
    inversion H5; subst. eapply e2t_det in H1; eauto; subst; constructor.
    inversion H5; subst. eapply e2t_det in H1; eauto; subst; constructor.

    inversion H1; subst. eapply e2t_det in H8; eauto; subst. eapply e2t_det in H9; eauto; subst.
    apply E_If. eapply IHt1; eauto.
  -
    inversion H0; subst.
    eapply e2t_det in H5; eauto; subst.
    eapply name_det in H4; eauto; subst. eapply e2t_det in H8; eauto; subst. apply E_App2.
    constructor. eapply IHt1; eauto.

    eapply e2t_det in H1; eauto; subst.
    rewrite <- (value_subst t1' t1'0 x).
    assert (abs x Unit ([x := t1'0]t1') = abs x Unit t1').
    rewrite (value_subst t1' t1'0 x). reflexivity.
    admit.
    rewrite H1.
    apply E_AppAbs. inversion H8; subst; inversion H6; subst; constructor.
    admit.
Admitted.

Open Scope string.

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


Reserved Notation "ctx '|-e' t '\in' T" (at level 40).
Inductive ehas_type : context -> Eterm -> ty -> Prop :=
  | eT_Var : forall ctx x T,
      ctx x = Some T ->
      ctx |-e Var x \in T
  | eT_Abs : forall ctx x T11 T12 t12,
      (x |-> T11 ; ctx) |-e t12 \in T12 ->
      ctx |-e Abs x T11 t12 \in Arrow T11 T12
  | eT_App : forall T11 T12 ctx t1 t2,
      ctx |-e t1 \in Arrow T11 T12 ->
      ctx |-e t2 \in T11 ->
      ctx |-e App t1 t2 \in T12
  | eT_Tru : forall ctx,
       ctx |-e Tru \in Bool
  | eT_Fls : forall ctx,
       ctx |-e Fls \in Bool
  | eT_If : forall t1 t2 t3 T ctx,
       ctx |-e t1 \in Bool ->
       ctx |-e t2 \in T ->
       ctx |-e t3 \in T ->
       ctx |-e EIf t1 t2 t3 \in T
  | eT_Seq : forall ctx t1 t2 T2,
      ctx |-e t1 \in Unit ->
      ctx |-e t2 \in T2 ->
      ctx |-e seq t1 t2 \in T2

where "ctx '|-e' t '\in' T" := (ehas_type ctx t T).


Theorem T11_3_1_2 : forall t ctx t' T,
    e2t t ctx t' ->
    ctx |-e t \in T <-> ctx |- t' \in T.
Proof.
  split;
  generalize dependent t'; generalize dependent T; generalize dependent ctx;
  induction t; intros; inversion H; subst; inversion H0; subst; auto; try solve [constructor; auto].

  eapply T_App; eauto.

  eapply T_App; eauto. apply T_Abs; auto.


  generalize dependent t'. generalize dependent T. generalize dependent ctx.
  induction t; intros; inversion H; subst; inversion H0; subst; auto; try solve [constructor; auto].

  apply eT_Abs; auto. eapply IHt in H7; eauto. admit.




End Seq.

End string.
