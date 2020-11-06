Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
From Coq Require Import Lists.List.
Import ListNotations.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Load "../std".

Inductive ty : Type :=
| Bool
|Arrow (ty1 ty2: ty).
Notation "t1 '|-->' t2" := (Arrow t1 t2) (at level 40).

Inductive term : Type :=
(*純粋λ計算*)
| Var (n: nat)
| Abs (name: string) (typ: ty) (t: term)
| App (t1 t2: term)
(*ぶーる*)
| Tru
| Fls
| If (t1 t2 t3: term).

Inductive value : term -> Prop :=
| V_tru : value Tru
| V_fls : value Fls
| V_abs :forall typ name t1, value (Abs typ name t1).

Definition context : Type :=
  list (string * ty).

Definition eqb_string s1 s2:=
  String.eqb s1 s2.

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

Definition isval t:=
match t with
| Tru => true
| Fls => true
| Abs _ _ _ => true
| _ => false
end.

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
    | (n1, b) :: m =>
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
    forall ctx n1 t,
      getbinding n1 ctx = Some t ->
      ctx |- (Var n1) \in t
| T_Abs:
    forall ctx x T1 t2 T2,
      ((x, T1) :: ctx) |- t2 \in T2 ->
      ctx |- (Abs x T1 t2) \in (T1 |--> T2)
| T_App:
    forall ctx t1 T11 T12 t2,
      ctx |- t1 \in (T11 |--> T12) ->
      ctx |- t2 \in T11 ->
      ctx |- App t1 t2 \in T12

where " ctx '|-' x '\in' t " := (has_type ctx x t).


Example type1:
  [("f"%string, (Bool |--> Bool))] |- App (Var 0) (If Fls Tru Fls) \in Bool.
Proof.
  eapply T_App. apply T_Var. reflexivity.
  apply T_If. apply T_False. apply T_True. apply T_False.
Qed.

Example type2:
  [("f"%string, (Bool |--> Bool))] |- (Abs "x" Bool (App (Var 1) (If (Var 0) Fls (Var 0)))) \in (Bool |--> Bool).
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

Fixpoint typeof ctx t : option ty :=
  match t with
  | Tru =>
    (Some Bool)
  | Fls =>
    Some Bool
  | If t1 t2 t3 =>
    match typeof ctx t1 with
    | Some Bool =>
      match typeof ctx t2 with
      | Some T2 =>
        match typeof ctx t3 with
        | Some T3 =>
          if eqb_ty T2 T3 then
            Some T2
          else
            None
        | None => None
        end
      | None => None
      end
    | _ => None
    end
  | Var n =>
    getbinding n ctx
  | Abs x T1 t1 =>
    match typeof ((x, T1) :: ctx) t1 with
    | Some T2 =>
      Some (T1 |--> T2)
    | None => None
    end
  | App t1 t2 =>
    match typeof ctx t1 with
    | Some (T11 |--> T12) =>
      match typeof ctx t2 with
      | Some T21 =>
        if eqb_ty T11 T21 then
          Some T12
        else
          None
      | None => None
      end
    | _ => None
    end
  end.

Lemma eq_type_refl : forall T,
    eqb_ty T T = true.
Proof.
  induction T; simpl; auto. rewrite IHT1, IHT2; auto.
Qed.

Lemma typeof_hasType : forall t ctx T,
    has_type ctx t T <-> typeof ctx t = Some T.
Proof.
  split; intros.
  -
    induction H; simpl; auto.
    +
      rewrite IHhas_type1, IHhas_type2, IHhas_type3. clear.
      rewrite eq_type_refl; reflexivity.
    +
      rewrite IHhas_type. reflexivity.
    +
      rewrite IHhas_type2, IHhas_type1. rewrite eq_type_refl; reflexivity.
  -
    generalize dependent T. generalize dependent ctx; induction t; intros; simpl; auto.
    +
      inversion H; subst; apply T_Var; simpl; auto.
    +
      inversion H; subst. destruct (typeof ((name, typ) :: ctx) t) eqn:IH. inversion H1; subst.
      apply IHt in IH. apply T_Abs. apply IH. inversion H1.
    +
      inversion H. destruct (typeof ctx t1) eqn:IH1. destruct (typeof ctx t2) eqn:IH2. apply IHt1 in IH1. apply IHt2 in IH2. destruct t. inversion H1. destruct (eqb_ty t3 t0) eqn:IH3. apply eqb_ty_eq in IH3. subst. inversion H1; subst. eapply T_App; eauto. inversion H1. destruct t. inversion H1. inversion H1. inversion H1.
    +
      inversion H. apply T_True.
    +
      inversion H. apply T_False.
    +
      inversion H. destruct (typeof ctx t1) eqn:IH1. destruct (typeof ctx t2) eqn:IH2. apply IHt1 in IH1. apply IHt2 in IH2. destruct (typeof ctx t3) eqn:IH3. apply IHt3 in IH3. destruct t.
      destruct (eqb_ty t0 t4) eqn:IH4. apply eqb_ty_eq in IH4. subst. inversion H1; subst. eapply T_If; eauto.
      inversion H1. inversion H1. destruct t; try solve_by_invert. destruct t; try solve_by_invert. inversion H1.
Qed.


Lemma leb_0_T : forall n,
    leb 0 n = true.
Proof.
  induction n; auto.
Qed.

Fixpoint in_free t n :=
  match t with
  | Var n1 =>
    if leb n n1 then
      true
    else
      false
  | Abs x T t1 =>
    in_free t1 (S n)
  | App t1 t2 =>
    in_free t1 n || in_free t2 n
  | Tru => false
  | Fls => false
  | If t1 t2 t3 =>
    in_free t1 n || in_free t2 n || in_free t3 n
  end.

Notation closed t := (in_free t 0 = false).

Lemma var_hastype_none : forall ctx,
    getbinding (length ctx) ctx = None.
Proof.
  induction ctx; auto.
Qed.

Lemma var_hastype_none_succ : forall n ctx,
    leb (length ctx) n = true ->
    getbinding n ctx = None.
Proof.
  induction n; intros; auto.
  destruct ctx; auto. simpl in H. inversion H.
  destruct ctx. simpl. reflexivity.
  simpl. apply IHn. apply leb_le. apply le_S_n. apply le_leb. apply H.
Qed.

Lemma closed_hastype : forall t T ctx,
    ctx |- t \in T ->
    in_free t (length ctx) = false.
Proof.
  induction t; intros; simpl; inversion H; subst; auto.
  destruct leb eqn:IH; auto. rewrite var_hastype_none_succ in H2. inversion H2. apply IH.
  apply IHt in H5. simpl in H5. apply H5.
  apply IHt1 in H3. apply IHt2 in H5. rewrite H3, H5; reflexivity.
  apply IHt1 in H4. apply IHt2 in H6. apply IHt3 in H7. rewrite H4, H6, H7; reflexivity.
Qed.

Lemma cosed_type_nil : forall t T,
    [] |- t \in T ->
    closed t.
Proof.
  intros. apply closed_hastype in H. simpl in H. apply H.
Qed.

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


(**)
Fixpoint shift (d k : nat) (t : term) : term :=
match t with
| Var x =>
  Var (if leb d x then x + k else x)
| Abs x T t' =>
  Abs x T (shift (S d) k t')
| App t1 t2 =>
  App (shift d k t1) (shift d k t2)
| Tru => Tru
| Fls => Fls
| If t1 t2 t3 =>
  If (shift d k t1) (shift d k t2) (shift d k t3)
end.

Fixpoint subst (d : nat) (s t: term) : term :=
match t with
| Var x =>
  if eqb_nat d x then (*d == x*)
    shift 0 d s
  else if ltb d x then (*d < x*)
         Var (pred x) else
         Var x (*d > x*)
| Abs x T t' => Abs x T (subst (S d) s t')
| App t1 t2 => App (subst d s t1) (subst d s t2)
| Tru => Tru
| Fls => Fls
| If t1 t2 t3 =>
  If (subst d s t1) (subst d s t2) (subst d s t3)
end.

Fixpoint eval (t: term) :=
  match t with
  | If t1 t2 t3 =>
    match t1 with
    | Tru => Some t2
    | Fls => Some t3
    | _ => match eval t1 with
          | Some t1' =>
            Some (If t1' t2 t3)
          | None => None
          end
    end
  | App t1 t2 =>
    if isval t1 then
      if isval t2 then
        match t1 with
        | Abs _ _ t12 => Some (subst 0 t2 t12)
        | _ => None
        end
      else
        match eval t2 with
        | Some t2' => Some (App t1 t2')
        | None => None
        end
    else
      match eval t1 with
      | Some t1' => Some (App t1' t2)
      | None => None
      end
  | _ => None
  end.

Compute (shift 0 1 (Abs _ _ (Var 1))).
Compute (subst 0 (App (Var 1) (Abs _ _ (Var 2))) (shift 1 1 (App (Var 0) (Abs _ _ (Var 1))))).
Compute (eval (App (Abs _ _ (App (Var 1) (App (Var 0) (Var 2)))) (Abs _ _ (Var 0)))).

(* (λ x. x)  λ y. y => λ y. y *)
Compute (eval (App (Abs "x" _ (Var 0)) (Abs "y" _ (Var 0)))).
(* TmAbs("y", TmVar(0, 1)) *)

(* (λ x. λ y. x) λ z. z => λ y. λ z. z *)
Compute (eval (App (Abs "x" _ (Abs "y" _ (Var 1))) (Abs "z" _ (Var 0)))).
 (* TmAbs("y", TmAbs("z", TmVar(0, 2))) *)

(* (λ x. λ x'. x) (λ x. x) => λ x'. λ x. x *)
Compute (eval (App (Abs "x" _ (Abs "x" _ (Var 1))) (Abs "x" _ (Var 0)))).
 (* TmAbs("x", TmAbs("x", TmVar(0, 2))) *)

(* (λ x. λ y. x) (λ z. z) (λ w. w) => (λ y. λ z. z) (λ w. w) *)
Compute (eval (App (App (Abs "x" _ (Abs "y" _ (Var 1))) (Abs "z" _ (Var 0))) (Abs "w" _ (Var 0)))).
(* TmApp(TmAbs("y", TmAbs("z", TmVar(0, 2))), TmAbs("w", TmVar(0, 1))) *)

(* (λ x. x) ((λ y. y) (λ z. z))  => (λ x. x) (λ z. z) *)
Compute (eval (App (Abs "x" _ (Var 0)) (App (Abs "y" _ (Var 0)) (Abs "z" _ (Var 0))))).
(* TmApp(TmAbs("x", TmVar(0, 1)), TmAbs("z", TmVar(0, 1))) *)

(* (λ x. x x) (λ x. x x) => (λ x. x x) (λ x. x x) *)
Compute (eval (App (Abs "x" _ (App (Var 0) (Var 0))) (Abs "x" _ (App (Var 0) (Var 0))))).
 (* TmApp(TmAbs("x", TmApp(TmVar(0, 1), TmVar(0, 1))), TmAbs("x", TmApp(TmVar(0, 1), TmVar(0, 1))) *)

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
    App (Abs typ str t12) t2 --> subst 0 t2 t12

  where " t '-->' t' " := (step t t').

Lemma shift0 : forall t n,
    shift n 0 t = t.
Proof.
  induction t; intros; simpl; eauto.
  rewrite <- plus_n_O. destruct leb; reflexivity.

  rewrite IHt; reflexivity.
  rewrite IHt1, IHt2; reflexivity.
  rewrite IHt1, IHt2, IHt3; reflexivity.
Qed.

Lemma shifting : forall t g g1 g2 T,
  (g1 ++ g) |- t \in T ->
  (g1 ++ g2 ++ g) |- (shift (length g1) (length g2) t) \in T.
Proof.
  induction t; intros; inversion H; subst; clear H; try solve [econstructor; eauto]; simpl.

  apply T_Var. destruct (leb) eqn:IH. apply le_leb in IH.
  generalize dependent g. generalize dependent T. generalize dependent n.
  induction g1; simpl; intros; eauto. rewrite appGetbind. apply H2.
  destruct n. inversion IH. simpl.
  apply le_S_n in IH. simpl in H2. eapply IHg1 in IH; eauto.

  apply leb_neq in IH. eapply length1_Some in IH. apply IH. apply H2.

  apply T_Abs.
  assert (S (length g1) = length ((name, typ) :: g1)). reflexivity.
  rewrite H. apply IHt with (g1:= ((name, typ) :: g1)). apply H5.
Qed.

Lemma gb_lt_add : forall ctx ctx' p T n,
  getbinding (S n) (ctx' ++ p :: ctx) = Some T ->
  length ctx' < S n ->
  getbinding n (ctx' ++ ctx) = Some T.
Proof.
  induction ctx'; simpl; intros; eauto.
  destruct n. inversion H0; subst. apply leb_le in H2; inversion H2.
  apply IHctx' in H. simpl. apply H. apply lt_S_n. apply H0.
Qed.

Lemma L9_3_8: forall t s x Ts T ctx ctx',
    (ctx' ++ (x, Ts) :: ctx) |- t \in T ->
    ctx |- s \in Ts ->
    (ctx' ++ ctx) |- subst (length ctx') s t \in T.
Proof.
  induction t; intros; inversion H; subst; clear H; try solve [econstructor; eauto]; simpl.
  destruct eqb_nat eqn:IHeq.
  apply eqb_eq in IHeq; subst. apply shifting with (g2 := ctx') (g1:= []) in H0; simpl in H0.
  rewrite <- (plus_O_n (length ctx')) in H3. rewrite (appGetbind ctx' ( (x, Ts) :: ctx) 0) in H3.
  simpl in H3. inversion H3; subst. apply H0.
  destruct ltb eqn:IHlt. apply ltb_lt in IHlt.
  destruct n. inversion IHlt. simpl. apply T_Var. clear H0.
  eapply gb_lt_add in H3; eauto.

  apply ltb_neq in IHlt. apply Nat.nlt_ge in IHlt. apply T_Var.
  apply le_lt_or_eq in IHlt. destruct IHlt.
  eapply length1_Some in H; eauto.
  subst. rewrite eqb_refl in IHeq; inversion IHeq.

  apply T_Abs. apply (IHt s x Ts T2 ctx ((name, typ) :: ctx')) in H6. simpl in H6. apply H6.
  apply H0.
Qed.

Theorem T9_3_9 : forall t t' T ctx,
    ctx |- t \in T ->
    t --> t' ->
    ctx |- t' \in T.
Proof.
  intros. generalize dependent T. induction H0; subst; simpl; intros; try solve [inversion H; subst; eauto].
  -
    inversion H; subst. apply IHstep in H5. apply T_If; auto.
  -
    inversion H; subst. apply IHstep in H4. apply T_App with T11; auto.
  -
    inversion H1; subst. apply IHstep in H7. apply T_App with T11; auto.
  -
    inversion H0; subst. clear H0. inversion H4; subst.
    apply (L9_3_8 t12 t2 typ T11 T ctx []) in H2; eauto.
Qed.

Extraction "./ocaml/deBruijin/src/eval" typeof eval.

Compute (subst 0 (Var 1) (shift 1 1 (App (Var 0) (Abs _ _ (Abs _ _ (Var 2)))))).
Compute (subst 0 (App (Var 1) (Abs _ _ (Var 2))) (shift 1 1 (App (Var 0) (Abs _ _ (Var 1))))).
Compute (subst 0 (Var 1) (shift 1 1 (Abs _ _ (App (Var 0) (Var 2))))).
Compute (subst 0 (Var 1) (shift 1 1 (Abs _ _  (App (Var 1) (Var 0))))).

Module not_proof.

Inductive N : Type :=
| P (n: nat)
| M1.

Fixpoint shift_walk c d t :=
  match t with
  | Var x =>
    if leb c x then
      match d with
      | M1 =>
        Var (x - 1)
      | P d' =>
        Var (x + d')
      end
    else
      Var x
  | Abs t x t1 =>
    Abs t x (shift_walk (S c) d t1)
  | App t1 t2 =>
    App (shift_walk c d t1) (shift_walk c d t2)
  | If t1 t2 t3 =>
    If (shift_walk c d t1) (shift_walk c d t2) (shift_walk c d t3)
  | _ => t
  end.

Notation shift d t := (shift_walk 0 d t).

Fixpoint sub_walk j s c t :=
  match t with
  | Var x =>
    let jc :=
        match c with
        | M1 => (j - 1)
        | P c' => (j + c')
        end
    in
    if eqb_nat x (jc) then
      shift c s
    else
      Var x
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

Notation sub j s t := (sub_walk j s (P 0) t).

Notation subtop s t := (shift M1 (sub 0 (shift (P 1) s) t)).


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



Lemma E9_3_2 :  forall n T,
    not (exists ctx,ctx |- App (Var n) (Var n) \in T).
Proof.
  intros; intro. inversion H.
  inversion H0; subst. inversion H4. inversion H6; subst.
  rewrite H9 in H3. inversion H3. apply eqb_ty_eq in H2.
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
    inversion H; inversion H0; subst. rewrite H3 in H7. inversion H7; reflexivity.
  -
    inversion H; inversion H0; subst.
    apply eqb_ty_eq. simpl; apply andb_true_intro; split; auto.
    clear. induction typ; auto. simpl. apply andb_true_intro. split; auto.
    apply eqb_ty_eq. apply (IHt1 ( (name, typ) :: ctx) T3 T5); auto.
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

Theorem T9_3_5 : forall t T,
    [] |- t \in T ->
    value t \/ exists t', t --> t'.
Proof.
  induction t; simpl; intros.
  -
    inversion H; subst. destruct n; inversion H2.
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

Lemma shift0_refl : forall t n,
    shift_walk n (P 0) t = t.
Proof.
  induction t; simpl; intros; auto.
  destruct (leb n0 n). rewrite <- plus_n_O. reflexivity.
  reflexivity. rewrite IHt. reflexivity.
  rewrite IHt1. rewrite IHt2. reflexivity.
  rewrite IHt1. rewrite IHt2. rewrite IHt3. reflexivity.
Qed.

Lemma shift_m1_p1_refl : forall t n,
    shift_walk n (M1) (shift_walk n (P 1) t) = t.
Proof.
  induction t; intros; simpl; auto.
  -
    destruct (leb n0 n) eqn:IH. simpl. apply le_leb in IH. apply PeanoNat.Nat.le_le_succ_r in IH. apply leb_le in IH. rewrite PeanoNat.Nat.add_1_r. rewrite IH. simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.

    simpl. rewrite IH. reflexivity.
  -
    rewrite IHt. reflexivity.
  -
    rewrite IHt2. rewrite IHt1. reflexivity.
  -
    rewrite IHt3, IHt2, IHt1.  reflexivity.
Qed.

Definition Minus1 n :=
    match n with
    | 0 => M1
    | S n => P n
    end.

Lemma shifting: forall t g g1 g2 T,
 (g1 ++ g) |- t \in T ->
 (g1 ++ g2 ++ g) |- (shift_walk  (length g1) (P (length g2)) t ) \in T.
Proof.
  induction t; simpl; intros; inversion H; subst; try solve [econstructor; eauto].

  destruct leb eqn:IH. apply T_Var.
  clear H. generalize dependent g. generalize dependent T. generalize dependent n.
  induction g1; simpl; intros; eauto. rewrite appGetbind. apply H2.
  destruct n. inversion IH.
  simpl. apply le_leb in IH. apply le_S_n in IH. apply leb_le in IH. simpl in H2. eapply IHg1 in IH; eauto.

  apply leb_neq in IH. eapply length1_Some in IH; eauto. apply T_Var. apply IH.

  inversion H; subst. apply T_Abs.
  assert (S (length g1) = length ((name, typ) :: g1) ). reflexivity. rewrite H0.
  assert ((name, typ) :: (g1 ++ g2 ++ g) = ((name, typ) :: g1) ++ g2 ++ g). reflexivity.
  rewrite H1. apply IHt. apply H5.
Qed.

Lemma shift_M1_succ : forall t n1 n2,
    shift_walk n1 (M1) (shift_walk n1 (P (S n2)) t) = shift_walk n1 (P n2) t.
Proof.
  induction t; intros; eauto; simpl.
  destruct (leb n1 n) eqn:IH1n; simpl.
  apply le_leb in IH1n. apply le_plus_trans with (p:= (S n2)) in IH1n. apply leb_le in IH1n. rewrite IH1n.
  rewrite Nat.add_succ_r. rewrite Nat.sub_1_r. reflexivity.
  rewrite IH1n. reflexivity.

  rewrite IHt. reflexivity.

  rewrite IHt1, IHt2; reflexivity.

  rewrite IHt1, IHt2, IHt3; reflexivity.
Qed.

Lemma len_get : forall ctx' x T ctx,
    getbinding (length ctx') (ctx' ++ (x, T) :: ctx) = Some T.
Proof.
  induction ctx'; intros; eauto. apply IHctx'.
Qed.

Lemma L9_3_8: forall t s x S T ctx,
    ((x, S) :: ctx) |- t \in T ->
    ctx |- s \in S ->
    ctx |- subtop s t \in T.
Proof.
  induction t; simpl; intros; simpl; try solve [inversion H; subst; econstructor; eauto].
   -
     rewrite shift0_refl.
     destruct (eqb_nat n 0) eqn:IH. apply eqb_eq in IH. subst.
     rewrite shift_m1_p1_refl. inversion H; subst. inversion H3; subst. apply H0.
     destruct n. inversion IH. simpl. rewrite leb_0_T. inversion H; subst. unfold getbinding in H3. simpl in H3. fold getbinding in H3. apply T_Var. rewrite PeanoNat.Nat.sub_0_r. apply H3.
   -
     inversion H; subst. apply T_Abs.
Admitted.

Theorem T9_3_9 : forall t t' T ctx,
    ctx |- t \in T ->
    t --> t' ->
    ctx |- t' \in T.
Proof.
  intros. generalize dependent T. induction H0; subst; simpl; intros; try solve [inversion H; subst; eauto].
  -
    inversion H; subst. apply IHstep in H5. apply T_If; auto.
  -
    inversion H; subst. apply IHstep in H4. apply T_App with T11; auto.
  -
    inversion H1; subst. apply IHstep in H7. apply T_App with T11; auto.
  -
    inversion H0; subst. clear H0.
    inversion H4; subst.

    eapply L9_3_8; eauto.
Qed.

Fixpoint eval (t: term) :=
  match t with
  | If t1 t2 t3 =>
    match t1 with
    | Tru => Some t2
    | Fls => Some t3
    | _ => match eval t1 with
          | Some t1' =>
            Some (If t1' t2 t3)
          | None => None
          end
    end
  | App t1 t2 =>
    if isval t1 then
      if isval t2 then
        match t1 with
        | Abs _ _ t12 => Some (subtop t2 t12)
        | _ => None
        end
      else
        match eval t2 with
        | Some t2' => Some (App t1 t2')
        | None => None
        end
    else
      match eval t1 with
      | Some t1' => Some (App t1' t2)
      | None => None
      end
  | _ => None
  end.

Lemma isval_no_step : forall t,
    isval t = true -> not (exists t', t --> t').
Proof.
  intros. destruct t; try solve_by_invert; intro;
  inversion H0; inversion H1.
Qed.

Lemma isval_value : forall t,
    value t <-> isval t = true.
Proof.
  split; intros; destruct t; try solve_by_invert; auto.
  apply V_abs. apply V_tru. apply V_fls.
Qed.

Lemma isval_F : forall t t',
    eval t = Some t' -> isval t = false.
Proof.
  intros. destruct t; try solve_by_invert; auto.
Qed.

Lemma isval_eval : forall t t',
    t --> t' ->
    isval t = false.
Proof.
  intros. inversion H; subst; auto.
Qed.

Lemma eval_step : forall t t',
    t --> t' <-> eval t = Some t'.
Proof.
  split; intros.
  -
    induction H; simpl; eauto.
    +
      rewrite IHstep. destruct t1; try solve_by_invert; auto.
    +
      rewrite IHstep. apply isval_eval in H. rewrite H. reflexivity.
    +
      rewrite IHstep. apply isval_eval in H0. rewrite H0. apply isval_value in H. rewrite H.
      reflexivity.
    +
      apply isval_value in H. rewrite H. reflexivity.
  -
    generalize dependent t'. induction t; intros; try solve_by_invert; auto; inversion H.
    +
      destruct (isval t1) eqn:IH1. destruct (isval t2) eqn:IH2.
      apply isval_value in IH1. inversion IH1; subst; try solve_by_invert.
      inversion H1. apply E_AppAbs. apply isval_value; auto.
      destruct (eval t2). inversion H1. apply E_App2. apply isval_value; auto. apply IHt2; auto.
      inversion H1.
      destruct (eval t1) eqn:IHH; try solve_by_invert. inversion H1. apply E_App1. apply IHt1; auto.
    +
      destruct (eval t1) eqn:IH; destruct t1; try solve_by_invert; inversion H1; try (apply E_If; apply IHt1; reflexivity). apply E_IfTrue. apply E_IfFalse.
Qed.

End not_proof.
