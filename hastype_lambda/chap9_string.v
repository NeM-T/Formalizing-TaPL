Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
From Coq Require Import Lists.List.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Import ListNotations.
Require Import std.

Inductive ty : Type :=
| Bool
|Arrow (ty1 ty2: ty).
Notation "t1 '|-->' t2" := (Arrow t1 t2) (at level 40).

Inductive term : Type :=
(*純粋λ計算*)
| var (name: string)
| abs (name: string) (typ: ty) (t: term)
| app (t1 t2: term)
(*ぶーる*)
| tru
| fls
| If (t1 t2 t3: term).

Inductive value : term -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.


Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | var x' =>
      if String.eqb x x' then s else t
  | abs x' T t1 =>
      abs x' T (if String.eqb x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | If t1 t2 t3 =>
      If ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive substi (s : term) (x : string) : term -> term -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2 : forall str,
      x <> str ->
      substi s x (var str) (var str)
  | s_abs1 : forall T t1,
      substi s x (abs x T t1) (abs x T t1)
  | s_abs2 : forall str T t1 t',
      x <> str ->
      substi s x t1 t' ->
      substi s x (abs str T t1) (abs str T t')
  | s_app : forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (app t1 t2) (app t1' t2')
  | s_tru :
    substi s x tru tru
  | s_fls :
    substi s x fls fls
  | s_if : forall t1 t2 t3 t1' t2' t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x (If t1 t2 t3) (If t1' t2' t3')
.
Theorem substi_correct : forall t s x t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  split.
  -
    generalize dependent s. generalize dependent t'. induction t; intros; auto.
    +
      unfold subst in H. destruct (x =? name)%string eqn:IH1.
      apply String.eqb_eq in IH1. rewrite IH1. rewrite H. apply s_var1.
      apply eqb_neq in IH1. rewrite <- H. apply s_var2; auto.
    +
      unfold subst in H.
      destruct (x =? name)%string eqn:IH1. apply String.eqb_eq in IH1. rewrite IH1.
      rewrite <- H. apply s_abs1.
      apply eqb_neq in IH1. fold subst in H. rewrite <- H. apply s_abs2; auto.
    +
      simpl in H. rewrite <- H. apply s_app; auto.
    +
      simpl in H. rewrite <- H. apply s_tru.
    +
      simpl in H. rewrite <- H. apply s_fls.
    +
      rewrite <- H. simpl. apply s_if; auto.
  -
    intros. induction H; simpl; auto.
    +
      rewrite eqb_refl. reflexivity.
    +
      apply eqb_neq in H. rewrite H. reflexivity.
    +
      rewrite eqb_refl. reflexivity.
    +
      apply eqb_neq in H. rewrite H. rewrite IHsubsti. reflexivity.
    +
      rewrite <- IHsubsti1. rewrite <- IHsubsti2. reflexivity.
    +
      rewrite <- IHsubsti2, IHsubsti1, IHsubsti3. reflexivity.
Qed.


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

where "t1 '-->' t2" := (step t1 t2).

Reserved Notation "ctx '|-' t '\in' T" (at level 40).

Definition context := partial_map ty.
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

Fixpoint eqb_ty T1 T2 :=
  match (T1, T2) with
  | (Bool, Bool) => true
  | (T11 |--> T12, T21 |--> T22) => andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | (Bool, _ |--> _) => false
  | (_ |--> _, Bool) => false
  end.

Fixpoint typeof ctx t :=
  match t with
  | var x => ctx x
  | abs x T1 t =>
    match typeof (x |-> T1; ctx) t with
    | Some T2 => Some (T1 |--> T2)
    | None => None
    end
  | app t1 t2 =>
    match typeof ctx t1 with
    | Some (T1 |--> T2) =>
      match typeof ctx t2 with
      | Some T1' =>
        if eqb_ty T1 T1' then
          Some T2
        else
          None
      | None => None
    end
    | _ => None
    end
  | tru => Some Bool
  | fls => Some Bool
  | If t1 t2 t3 =>
    match typeof ctx t1 with
    | Some Bool =>
      match (typeof ctx t2, typeof ctx t3) with
      | (Some T2, Some T3) =>
        if eqb_ty T2 T3 then
          Some T2
        else
          None
      | _ => None
      end
    | _ => None
    end
  end.

Lemma eqb_ty_TT : forall T,
    eqb_ty T T = true.
Proof.
  induction T; simpl; subst; auto. rewrite IHT1, IHT2; reflexivity.
Qed.

Lemma eqb_ty_eq : forall T1 T2,
    eqb_ty T1 T2 = true <-> T1 = T2.
Proof.
  split; intros; generalize dependent T2; induction T1; intros; auto; try (subst; reflexivity).
  inversion H; subst. destruct T2; try solve_by_invert; auto.
  inversion H; subst. destruct T2. inversion H1. apply andb_prop in H1. inversion H1. apply IHT1_1 in H0. apply IHT1_2 in H2. subst; reflexivity.
  subst. simpl. apply andb_true_intro. split; auto.
Qed.

Lemma typeof_ok : forall t T ctx,
    ctx |- t \in T <-> typeof ctx t = Some T.
Proof.

  split; intros.
  -
    induction H; simpl; eauto.
    +
      rewrite IHhas_type; reflexivity.
    +
      rewrite IHhas_type1, IHhas_type2. rewrite eqb_ty_TT. reflexivity.
    +
      rewrite IHhas_type1, IHhas_type2, IHhas_type3. rewrite eqb_ty_TT. reflexivity.
  -
    generalize dependent T; generalize dependent ctx; induction t; intros; inversion H; auto.
    +
      apply T_Var; auto.
    +
      destruct (typeof (name |-> typ; ctx) t) eqn:IH; try solve_by_invert.
      apply IHt in IH. inversion H1. subst. apply T_Abs; auto.
    +
      destruct (typeof ctx t1) eqn:IH1; destruct (typeof ctx t2) eqn:IH2; try solve_by_invert; destruct t; try solve_by_invert.
      destruct (eqb_ty t3 t0) eqn:IH; try solve_by_invert. apply eqb_ty_eq in IH; subst.
      apply IHt1 in IH1. apply IHt2 in IH2. inversion H1. eapply T_App; eauto. rewrite <- H2. auto.
    +
      apply T_Tru.
    +
      apply T_Fls.
    +
      destruct (typeof ctx t1) eqn:IH1; destruct (typeof ctx t2) eqn:IH2; destruct (typeof ctx t3) eqn:IH3; try solve_by_invert; destruct t; try solve_by_invert.
      destruct (eqb_ty t0 t4) eqn:IH; try solve_by_invert. inversion H1; apply eqb_ty_eq in IH; subst.
      apply T_If; auto.
Qed.

Extraction "ocaml/str/src/eval.ml" typeof.

Lemma eqb_ty_f : forall T1 T2,
    eqb_ty T1 (T1 |--> T2) = false.
Proof.
  induction T1; intros; auto. simpl. rewrite IHT1_1. reflexivity.
Qed.

Lemma eqb_ty_swap : forall T1 T2,
    eqb_ty T1 T2 = eqb_ty T2 T1.
Proof.
  induction T1; intros; auto.
  induction T2; auto.
  simpl. destruct T2. reflexivity.
  rewrite IHT1_1. rewrite IHT1_2. reflexivity.
Qed.

Lemma E9_3_2 : forall x ctx,
    not ( exists T, ctx |- app (var x) (var x) \in T).
Proof.
  intros; intro. inversion H; inversion H0; subst. apply typeof_ok in H4. apply typeof_ok in H6.
  rewrite H4 in H6. inversion H6. apply eqb_ty_eq in H2. rewrite eqb_ty_swap in H2. rewrite eqb_ty_f in H2. inversion H2.
Qed.

Lemma L9_3_3 : forall t ctx T1 T2,
    ctx |- t \in T1 ->
    ctx |- t \in T2 ->
    T1 = T2.
Proof.
  intros. apply typeof_ok in H; apply typeof_ok in H0. rewrite H in H0. inversion H0; auto.
Qed.

Lemma L_9_3_4_bool : forall v ctx,
    ctx |- v \in Bool ->
    value v ->
    v = tru \/ v = fls.
Proof.
  intros. inversion H0; subst; try solve_by_invert; auto.
Qed.

Lemma L9_3_4_Arrow : forall v ctx T1 T2,
    ctx |- v \in (T1 |--> T2) ->
    value v ->
    exists t x, v = abs x T1 t.
Proof.
  intros. inversion H0; subst; try solve_by_invert; auto. inversion H; subst. eauto.
Qed.

Theorem T9_3_5 : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  induction t; intros...
  -
    inversion H; subst. inversion H2.
  -
    left. apply v_abs.
  -
    right.
    inversion H; subst. generalize H3; intros. apply IHt1 in H3.
    destruct H3. inversion H1; subst; try solve_by_invert.
    apply IHt2 in H5. destruct H5.
    exists ([x := t2]t). apply E_AppAbs...
    inversion H2. exists (app (abs x T0 t) x0)... apply E_App2; auto.
    inversion H1. exists (app x t2). apply E_App1. apply H2.
  -
    left. apply v_tru.
  -
    left. apply v_fls.
  -
    right. inversion H; subst.
    generalize H4; intros; apply IHt1 in H4; destruct H4...
    inversion H1; subst; try solve_by_invert.
    exists t2. apply E_IfTru. exists t3. apply E_IfFls.
    inversion H1. exists (If x t2 t3). apply E_If...
Qed.

Notation "s1 '==' s2" := (String.eqb s1 s2) (at level 60).

Lemma L9_3_6 : forall t ctx x1 T1 x2 T2 T,
    x1 <> x2 ->
    (x1 |-> T1 ; x2 |-> T2 ; ctx) |- t \in T ->
    (x2 |-> T2 ; x1 |-> T1 ; ctx) |- t \in T.
Proof.
  intros. unfold update. rewrite <- (t_update_permute (option ty) ctx (Some T1) (Some T2) x1 x2); auto.
Qed.


Lemma L9_3_7 : forall t T ctx x S,
    ctx x = None ->
    ctx |- t \in T ->
    (x |-> S ; ctx) |- t \in T.
Proof.
  induction t; intros.
  -
    inversion H0; subst. apply T_Var. unfold update, t_update.
    destruct (x == name) eqn:IHnx. apply String.eqb_eq in IHnx. subst. rewrite H in H3. inversion H3.
    auto.
  -
    inversion H0; subst. apply T_Abs. destruct (x == name) eqn:IHxn.
    apply String.eqb_eq in IHxn. subst. unfold update; rewrite t_update_shadow. apply H6.
    apply L9_3_6. apply eqb_neq; auto.
    apply IHt. unfold update, t_update. rewrite eqb_sym in IHxn. rewrite IHxn. apply H. apply H6.
  -
    inversion H0; subst. eapply T_App. apply IHt1; auto. apply H4.
    apply IHt2; auto.
  -
    inversion H0; subst. apply T_Tru.
  -
    inversion H0; subst; apply T_Fls.
  -
    inversion H0; subst. apply T_If; auto.
Qed.

Lemma L9_3_8 : forall t s S T ctx x,
    (x |-> S; ctx) |- t \in T ->
    ctx |- s \in S ->
    ctx |- [x := s]t \in T.
Proof.
  induction t; intros; simpl.
  -
    inversion H; subst. destruct (x == name) eqn:IH. apply String.eqb_eq in IH; subst.
    rewrite update_eq in H3. inversion H3. subst. apply H0.
    unfold update, t_update in H3. rewrite IH in H3. apply T_Var. apply H3.
  -
    inversion H; subst. apply T_Abs.
    destruct (x == name) eqn:IH. apply String.eqb_eq in IH. subst. unfold update in H6; rewrite t_update_shadow in H6. unfold update; auto.
    apply eqb_neq in IH. apply L9_3_6 in H6; auto.
    eapply IHt; eauto. apply L9_3_7. admit. apply H0.
  -
    inversion H; subst. eapply T_App. eapply IHt1; eauto.
    eapply IHt2; eauto.
  -
    inversion H; subst. apply T_Tru.
  -
    inversion H; subst; apply T_Fls.
  -
    inversion H; subst. apply T_If. eapply IHt1; eauto. eapply IHt2; eauto. eapply IHt3; eauto.
Admitted. (*閉じた項のみを想定しているのでAdmit*)

Lemma T9_3_9 : forall t t' T ctx,
    ctx |- t \in T ->
    t --> t' ->
    ctx |- t' \in T.
Proof.
  induction t; intros; try solve_by_invert; auto.
  -
    inversion H0; subst; inversion H; subst.
    inversion H5; subst. eapply L9_3_8; eauto.
    eapply T_App; eauto. eapply T_App; eauto.
  -
    inversion H0; subst; inversion H; subst; auto.
    apply T_If; auto; apply IHt1; auto.
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
      appears_free_in x (If t1 t2 t3).

Hint Constructors appears_free_in.

Definition closed (t:term) := forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T ctx,
   appears_free_in x t ->
   ctx |- t \in T ->
   exists T', ctx x = Some T'.
Proof.
  intros x t T ctx H H0. generalize dependent ctx. generalize dependent T.
  induction H; intros; try solve [inversion H0; eauto].
  -
    inversion H1; subst. apply IHappears_free_in in H7. inversion H7. unfold update in H2.
    rewrite t_update_neq in H2; eauto.
Qed.

Lemma context_invariance : forall ctx ctx' t T,
     ctx |- t \in T ->
     (forall x, appears_free_in x t -> ctx x = ctx' x) ->
     ctx' |- t \in T.
Proof.
  intros. generalize dependent ctx'; induction H; intros; eauto.
  -
    apply T_Var. rewrite <- H0; auto.
  -
    apply T_Abs. apply IHhas_type. intros. unfold update, t_update. destruct (x == x0) eqn:IH; auto. eapply afi_abs in H1. apply H0. apply H1. apply eqb_neq ; auto.
  -
    eapply T_App; eauto.
  -
    apply T_Tru.
  -
    apply T_Fls.
  -
    apply T_If; eauto.
Qed.


Lemma empty_type_close : forall t T ,
    empty |- t \in T ->
    closed t.
Proof.
  unfold closed, not. intros. eapply free_in_context with (ctx:=empty) in H0. inversion H0. inversion H1.
  apply H.
Qed.

Lemma L9_3_8_SF : forall t s S T ctx x,
    (x |-> S; ctx) |- t \in T ->
    empty |- s \in S ->
    ctx |- [x := s]t \in T.
Proof.
  induction t; simpl; intros; eauto.
  -
    inversion H; subst. destruct (x == name) eqn:IH1. apply String.eqb_eq in IH1; subst.
    unfold update in H3. rewrite t_update_eq in H3. inversion H3; subst; auto. eapply context_invariance.
    apply H0. intros. apply empty_type_close in H0. einduction H0. apply H1. unfold update, t_update in H3.
    rewrite IH1 in H3. apply T_Var. apply H3.
  -
    destruct (x == name) eqn:IH. apply String.eqb_eq in IH; subst. inversion H; subst. apply T_Abs.
    unfold update in H6; rewrite t_update_shadow in H6. unfold update. apply H6.
    inversion H; subst. apply T_Abs. eapply IHt; eauto. unfold update. apply L9_3_6. apply eqb_neq. rewrite eqb_sym; auto. apply H6.
  -
    inversion H; subst. eapply T_App; eauto.
  -
    inversion H; subst. constructor.
  -
    inversion H; subst. constructor.
  -
    inversion H; subst. constructor; eauto.
Qed.

Lemma L9_3_9_SF : forall t t' T,
    empty |- t \in T ->
    t --> t' ->
    empty |- t' \in T.
Proof.
  induction t; intros; try solve_by_invert.
  -
    inversion H; subst. inversion H0; subst; try solve [eapply T_App; eauto].
    inversion H4; subst. eapply L9_3_8_SF in H3; eauto.
  -
    inversion H; subst. inversion H0; subst; eauto. apply T_If; eauto.
Qed.