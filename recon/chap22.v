Load "./syntax".
Import Nat.

Fixpoint match_natlist {A: Type} (l: list (nat * A)) n def :=
  match l with
  | [] => def
  | (n1, h) :: t => if eqb n1 n then h else match_natlist t n def
  end.

Fixpoint subst_type l t :=
  match t with
  | TyVar n => match_natlist l n t
  | Bool => Bool
  | Arrow t1 t2 =>
    subst_type l t1 |--> subst_type l t2 
  end.

Fixpoint subst_type_term l t :=
  match t with
  | Var n => Var n
  | Abs x typ e1 =>
    Abs x (subst_type l typ) (subst_type_term l e1)
  | Tru => Tru
  | Fls => Fls
  | App e1 e2 => App (subst_type_term l e1) (subst_type_term l e2)
  | If e1 e2 e3 => If (subst_type_term l e1) (subst_type_term l e2) (subst_type_term l e3)
  end.

Definition subst_type_list subl (ctx: context) := map (subst_type subl) ctx.

Theorem T22_1_2 : forall Γ σ t T,
    Γ |- t \in T -> subst_type_list σ Γ |- subst_type_term σ t \in subst_type σ T.
Proof.
  intros. generalize dependent σ. induction H; simpl; intros; try solve [econstructor; eauto].
  -
    constructor; eauto. generalize dependent n1.
    induction ctx; simpl; intros; simpl in H; auto.
    destruct n1; simpl in H; try discriminate.
    destruct n1. simpl. simpl in H. inversion H; subst. reflexivity.
    simpl. simpl in H. apply IHctx in H. apply H.
Qed.

Fixpoint tyn_in_type n ty :=
  match ty with
  | TyVar n1 => eqb n n1
  | t1 |--> t2 => (tyn_in_type n t1) || (tyn_in_type n t2)
  | _ => false
  end.

Fixpoint tyn_in_term n t :=
  match t with
  | App e1 e2 => (tyn_in_term n e1) || (tyn_in_term n e2)
  | Abs x typ e1 => if tyn_in_type n typ then true else (tyn_in_term n e1)
  | If e1 e2 e3 => (tyn_in_term n e1) || (tyn_in_term n e2) || (tyn_in_term n e3)
  | _ => false
  end.

Fixpoint tyn_in_list n l :=
  match l with
  | [] => false
  | ty :: t => (tyn_in_type n ty) || (tyn_in_list n t)
  end.

Fixpoint max_tyvar_type n ty :=
  match ty with
  | TyVar m => if ltb n m then m else n
  | ty1 |--> ty2 =>
    let n1 := max_tyvar_type n ty1 in
    let n2 := max_tyvar_type n ty2 in
    if ltb n1 n2 then n2 else n1
  | _ => n
  end.

Fixpoint max_tyvar_term n t :=
  match t with
  | Abs _ ty e1 =>
    let n1 := max_tyvar_type n ty in
    let n2 := max_tyvar_term n e1 in
    if ltb n1 n2 then n2 else n1
  | App e1 e2 =>
    let n1 := max_tyvar_term n e1 in
    let n2 := max_tyvar_term n e2 in
    if ltb n1 n2 then n2 else n1
  | If e1 e2 e3 =>
    let n1 := max_tyvar_term n e1 in
    let n2 := max_tyvar_term n e2 in
    let n3 := max_tyvar_term n e3 in
    let r := if ltb n1 n2 then n2 else n1 in
    if ltb r n3 then n3 else r
  | _ => n
  end.

Fixpoint max_tyvar_list n l :=
  match l with
  | [] => n
  | h :: t =>
    let m := max_tyvar_type n h in
    let r := if ltb n m then m else n in
    max_tyvar_list r t
  end.

Lemma Smax_tyvar_type_is_not_in : forall typ n n1,
    max_tyvar_type n typ < n1 ->
    tyn_in_type n1 typ = false.
Proof.
  induction typ; simpl; intros; auto.
  -
    destruct ltb eqn:IH1.
    apply Nat.ltb_lt in IH1. apply Nat.lt_trans with (p:= n1) in IH1; auto.
    apply IHtyp1 in IH1. apply IHtyp2 in H. rewrite IH1, H. reflexivity.
    apply Nat.ltb_ge in IH1. apply Nat.le_lt_trans with (p:= n1) in IH1; auto.
    apply IHtyp1 in H. apply IHtyp2 in IH1. rewrite IH1, H; reflexivity.
  -
    destruct ltb eqn:IH.
    +
      apply Nat.lt_neq in H. apply Nat.eqb_neq in H. rewrite Nat.eqb_sym in H. rewrite H. reflexivity.
    +
      apply Nat.ltb_ge in IH. apply Nat.le_lt_trans with (p:= n1) in IH; auto.
      rewrite Nat.eqb_sym. apply Nat.lt_neq in IH. apply Nat.eqb_neq in IH. rewrite IH. reflexivity.
Qed.

Lemma Smax_tyvar_term_is_not_in : forall e n m,
    max_tyvar_term n e < m ->
    tyn_in_term m e = false.
Proof.
  induction e; simpl; intros; auto.
  -
    destruct ltb eqn:IH.
    assert (tyn_in_type m typ = false).
    +
      apply Smax_tyvar_type_is_not_in with n. apply Nat.ltb_lt in IH.
      apply Nat.lt_trans with (max_tyvar_term n e); auto.
    +
      rewrite H0. apply IHe in H. apply H.
    +
      apply Nat.ltb_ge in IH. apply Nat.le_lt_trans with (p:= m) in IH; auto. apply IHe in IH.
      apply Smax_tyvar_type_is_not_in in H. rewrite IH, H. reflexivity.
  -
    destruct ltb eqn:IH.
    +
      apply Nat.ltb_lt in IH. apply Nat.lt_trans with (p:= m) in IH; auto.
      apply IHe1 in IH. apply IHe2 in H. rewrite IH, H; reflexivity.
    +
      apply Nat.ltb_ge in IH. eapply Nat.le_lt_trans in IH; eauto.
      apply IHe1 in H. apply IHe2 in IH. rewrite IH, H; reflexivity.
  -
    destruct (max_tyvar_term n e1 <? max_tyvar_term n e2) eqn:IH1.
    +
      destruct (max_tyvar_term n e2 <? max_tyvar_term n e3) eqn:IH2.
      ++
        apply Nat.ltb_lt in IH2. apply Nat.ltb_lt in IH1.
        apply Nat.lt_trans with (p:= m) in IH2; auto.
        apply Nat.lt_trans with (p:= m) in IH1; auto.
        apply IHe1 in IH1. apply IHe2 in IH2. apply IHe3 in H.
        rewrite IH1, IH2, H; reflexivity.
      ++
        apply Nat.ltb_lt in IH1. apply Nat.ltb_ge in IH2.
        apply Nat.lt_trans with (p:= m) in IH1; auto.
        apply Nat.le_lt_trans with (p:= m) in IH2; auto.
        apply IHe1 in IH1. apply IHe2 in H. apply IHe3 in IH2.
        rewrite IH1, IH2, H; reflexivity.
    +
      apply Nat.ltb_ge in IH1.
      destruct (max_tyvar_term n e1 <? max_tyvar_term n e3) eqn:IH2.
      ++
        apply Nat.ltb_lt in IH2. apply Nat.lt_trans with (p:= m) in IH2; auto.
        apply Nat.le_lt_trans with (p:= m) in IH1; auto.
        apply IHe1 in IH2. apply IHe2 in IH1. apply IHe3 in H.
        rewrite IH1, IH2, H; reflexivity.
      ++
        apply Nat.ltb_ge in IH2.
        apply Nat.le_lt_trans with (p:= m) in IH1; auto.
        apply Nat.le_lt_trans with (p:= m) in IH2; auto.
        apply IHe1 in H. apply IHe2 in IH1. apply IHe3 in IH2.
        rewrite H, IH1, IH2; reflexivity.
Qed.

Lemma max_tyvar_list_n_lt_m : forall l n m,
    max_tyvar_list n l < m ->
    n < m.
Proof.
  induction l; simpl; intros; eauto.
  destruct ltb eqn:IH; eauto.
  apply Nat.ltb_lt in IH. apply Nat.lt_trans with (p:= m) in IH; auto.
Qed.

Lemma Smax_tyvar_list_is_not_in : forall l n m,
    max_tyvar_list n l < m ->
    tyn_in_list m l = false.
Proof.
  induction l; simpl; intros; auto.
  destruct ltb eqn:IH.
  -
    erewrite IHl; eauto.
    apply max_tyvar_list_n_lt_m in H. apply Smax_tyvar_type_is_not_in in H.
    rewrite H. reflexivity.
  -
    apply Nat.ltb_ge in IH.
    apply Nat.le_lt_trans with (p:= m) in IH.
    apply Smax_tyvar_type_is_not_in in IH.
    erewrite IHl; eauto.
    rewrite IH. reflexivity.
    apply max_tyvar_list_n_lt_m in H; apply H.
Qed.

Definition max_tyvar_list_term n l e :=
  let n1 := max_tyvar_list n l in
  let m := max_tyvar_term n e in
  if ltb n1 m then m else n1.

Lemma max_tyvar_list_term_is_not_in : forall n l e m,
    max_tyvar_list_term n l e < m ->
    tyn_in_list m l = false /\ tyn_in_term m e = false.
Proof.
  intros. unfold max_tyvar_list_term in H.
  destruct ltb eqn:IH.
  -
    apply Nat.ltb_lt in IH.
    apply Nat.lt_trans with (p:= m) in IH; auto.
    apply Smax_tyvar_list_is_not_in in IH. rewrite IH.
    apply Smax_tyvar_term_is_not_in in H. rewrite H. split; reflexivity.
  -
    apply Nat.ltb_ge in IH.
    apply Nat.le_lt_trans with (p:= m) in IH; auto.
    apply Smax_tyvar_term_is_not_in in IH.
    apply Smax_tyvar_list_is_not_in in H.
    auto.
Qed.    

Reserved Notation "Γ |-- n ` t \in T | m ` C "(at level 50).
Inductive Constrait_Type : context -> nat -> term -> ty -> nat -> list (ty * ty) -> Prop :=
| CT_Var : forall x T Γ F,
    getbinding x Γ = Some T ->
    Γ |-- F ` Var x \in T | F ` []
| CT_Abs : forall Γ x T1 t2 T2 C F' F,
    (T1:: Γ) |-- F ` t2 \in T2 | F' ` C ->
    Γ |-- F ` (Abs x T1 t2) \in T1 |--> T2 | F' ` C
| CT_App : forall Γ t1 ty1 C1 t2 ty2 C2 F' F'' F,
    Γ |-- F ` t1 \in ty1 | F' ` C1 -> Γ |-- F' ` t2 \in ty2 | F'' ` C2 ->
    Γ |-- F ` App t1 t2 \in (TyVar (S F'')) | (S F'') ` ((ty1, ty2 |--> TyVar (S F'') ) :: C1 ++ C2)
| CT_Tru : forall Γ F,
    Γ |-- F ` Tru \in Bool | F ` []
| CT_Fls : forall Γ F,
    Γ |-- F ` Fls \in Bool | F ` []
| CT_If : forall e1 e2 e3 ty1 ty2 ty3 F1 F2 F3 C1 C2 C3 Γ F,
    Γ |-- F ` e1 \in ty1 | F1 ` C1 -> Γ |-- F1 ` e2 \in ty2 | F2 ` C2 ->
    Γ |-- F2 ` e3 \in ty3 | F3 ` C3 -> 
    Γ |-- F ` If e1 e2 e3 \in ty3 | F3 ` ( (ty1, Bool):: (ty2, ty3) :: C1 ++ C2 ++ C3 )
where "Γ |-- n ` t \in T | m ` C" := (Constrait_Type Γ n t T m C).

Fixpoint Constrait_Type_fix Γ n e :=
  match e with
  | Var x => match getbinding x Γ with
             | Some ty => Some (ty, n, nil)
             | None => None
             end
  | Abs _ ty1 e1 =>
    match Constrait_Type_fix (ty1 :: Γ) n e1 with
    | Some (ty, n1, l) => Some (ty1 |--> ty, n1, l)
    | None => None
    end
  | App e1 e2 =>
    match Constrait_Type_fix Γ n e1 with
    | Some (ty1, n1, C1) =>
      match Constrait_Type_fix Γ n1 e2 with
      | Some (ty2, n2, C2) =>
        Some (TyVar (S n2), S n2, (ty1, ty2 |--> (TyVar (S n2)) ):: C1 ++ C2)
      | None => None
      end
    | None => None
    end
  | Tru => Some (Bool, n, nil)
  | Fls => Some (Bool, n, nil)
  | If e1 e2 e3 =>
    match Constrait_Type_fix Γ n e1 with
    | Some (ty1, n1, C1) =>
      match Constrait_Type_fix Γ n1 e2 with
      | Some (ty2, n2, C2) =>
        match Constrait_Type_fix Γ n2 e3 with
        | Some (ty3, n3, C3) => Some (ty3, n3, (ty1, Bool):: (ty2, ty3) :: C1 ++ C2 ++ C3)
        | Noen => None
        end
      | None => None
      end
    | None => None
    end
  end.

Lemma Constrait_Type_fix_Correct1 : forall Γ n e typ m C,
    Γ |-- n ` e \in typ | m ` C -> Constrait_Type_fix Γ n e = Some (typ, m, C).
Proof.
  intros.
  induction H; simpl; auto.
  +
    rewrite H. reflexivity.
  +
    rewrite IHConstrait_Type. reflexivity.
  +
    rewrite IHConstrait_Type1, IHConstrait_Type2. reflexivity.
  +
    rewrite IHConstrait_Type1, IHConstrait_Type2, IHConstrait_Type3; reflexivity.
Qed.

Lemma Constrait_Type_fix_Correct2 : forall e Γ n typ m C,
    Constrait_Type_fix Γ n e = Some(typ, m, C) -> Γ |-- n ` e \in typ | m ` C.
Proof.
  induction e; simpl; intros; auto.
  -
    destruct getbinding eqn:IH; try discriminate.
    inversion H; subst. constructor. rewrite IH. reflexivity.
  -
    destruct Constrait_Type_fix eqn:IH; try discriminate.
    destruct p. destruct p. apply IHe in IH. inversion H; subst.
    econstructor; eauto.
  -
    destruct Constrait_Type_fix eqn:IH1; try discriminate.
    destruct p. destruct p. apply IHe1 in IH1.
    destruct Constrait_Type_fix eqn:IH2; try discriminate.
    destruct p. destruct p. apply IHe2 in IH2.
    inversion H; subst.
    econstructor; eauto.
  -
    inversion H; subst; constructor.
  -
    inversion H; subst; constructor.
  -
    destruct Constrait_Type_fix eqn:IH1; try discriminate.
    destruct p. destruct p. apply IHe1 in IH1.
    destruct Constrait_Type_fix eqn:IH2; try discriminate.
    destruct p. destruct p. apply IHe2 in IH2.
    destruct Constrait_Type_fix eqn:IH3; try discriminate.
    destruct p. destruct p. apply IHe3 in IH3.
    inversion H; subst.
    econstructor; eauto.
Qed.

Definition CT_fix Γ e := Constrait_Type_fix Γ (max_tyvar_list_term 0 Γ e) e.

Compute (CT_fix []  (Abs "x" (TyVar 0) (Abs "y" (TyVar 1) (Abs "z" (TyVar 2)
           (App (App (Var 2) (Var 0) ) (App (Var 1) (Var 0)) )) ))).

Fixpoint Constrais_sol_bool σ C :=
  match C with
  | nil => true
  | (ty1, ty2) :: t =>
    if eqb_ty (subst_type σ ty1) (subst_type σ ty2) then
      (Constrais_sol_bool σ t)
    else false
  end.

Lemma Constrais_sol_bool_app : forall σ C1 C2,
    Constrais_sol_bool σ (C1 ++ C2) = true ->
    Constrais_sol_bool σ C1 = true /\ Constrais_sol_bool σ C2 = true.
Proof.
  induction C1; simpl; intros; auto.
  destruct a.
  destruct eqb_ty; try discriminate.
  apply IHC1 in H. apply H.
Qed.

Theorem T22_3_5 : forall e Γ S C σ T n m,
    Γ |-- n ` e \in S | m ` C ->
    subst_type σ S = T -> Constrais_sol_bool σ C = true ->
    subst_type_list σ Γ |- subst_type_term σ e \in T.
Proof.
  induction e; simpl; intros; auto.
  -
    rewrite <- H0.
    inversion H; subst.
    assert (Var n = subst_type_term σ (Var n)). reflexivity.
    rewrite H0.
    apply T22_1_2. constructor; auto.
  -
    inversion H; subst.
    eapply IHe in H10; eauto.
    constructor. apply H10.
  -
    inversion H; subst.
    simpl in H1.
    destruct eqb_ty eqn:IH1; try discriminate.
    apply eqb_ty_eq in IH1; subst.
    apply Constrais_sol_bool_app in H1. destruct H1.
    econstructor; eauto.
  -
    inversion H; subst. simpl. constructor.
  -
    inversion H; subst. simpl. constructor.
  -
    inversion H; subst. simpl in H1.
    destruct eqb_ty eqn:IH1; try discriminate.
    apply eqb_ty_eq in IH1; subst.
    destruct eqb_ty eqn:IH2; try discriminate.
    apply eqb_ty_eq in IH2; subst.
    apply Constrais_sol_bool_app in H1. destruct H1.
    apply Constrais_sol_bool_app in H1; destruct H1.
    constructor; eauto.
Qed.

Lemma app_Constrais_sol_bool : forall σ C1 C2,
    Constrais_sol_bool σ C1 = true -> Constrais_sol_bool σ C2 = true ->
    Constrais_sol_bool σ (C1 ++ C2) = true.
Proof.
  induction C1; simpl; intros; auto.
  destruct a. destruct eqb_ty; try discriminate.
  apply IHC1; auto.
Qed.    

Lemma getbind_sub : forall σ Γ n T S,
  getbinding n (subst_type_list σ Γ) = Some T ->
  getbinding n Γ = Some S ->
  subst_type σ S = T.
Proof.
  induction Γ; simpl; intros.
  -
    destruct n; discriminate.
  -
    destruct n; simpl in H, H0.
    inversion H0; subst. inversion H; subst. reflexivity.
    eapply IHΓ; eauto.
 Qed.   

Fixpoint max_sigma n (σ: list (nat * ty) ) :=
  match σ with
  | nil => n
  | (m, _):: rest =>
    let x := if ltb n m then m else n in
    max_sigma x rest
  end.

Lemma CT_n_lt : forall e Γ n typ m C,
    Γ |-- n ` e \in typ | m ` C -> n <= m.
Proof.
  intros. induction H; auto.
  -
    eapply le_trans with (p:= F'') in IHConstrait_Type1; eauto. 
  -
    eapply le_trans with (p:= F2) in IHConstrait_Type1; eauto. 
    eapply le_trans with (p:= F3) in IHConstrait_Type1; eauto. 
Qed.

Fixpoint dom_sigma_in n (σ :list (nat * ty)) :=
  match σ with
  | nil => false
  | (m, _) :: rest => if eqb n m then true else dom_sigma_in n rest
  end.

Fixpoint dom_sigma_in_range n m σ :=
  match m with
  | 0 => false
  | S m' => dom_sigma_in (S n) σ || dom_sigma_in_range (S n) m' σ
  end.

Lemma dom_sigma_range_correct : forall m n σ,
    dom_sigma_in_range n m σ = false ->
    (forall x, n <= S x -> x <= (n + m) -> dom_sigma_in x σ = false).
Proof.
Abort.

Fixpoint create_sigma n m l : option (list (nat * ty)) :=
  match m, l with
  | 0, nil => Some nil
  | S m', h:: t =>
    match create_sigma (S n) m' t with
    | Some t' => Some ((S n, h):: t')
    | None => None
    end
  | _, _ => None
  end.

Fixpoint subst_type_opt l t n m :=
  match t with
  | Bool => Some Bool
  | TyVar x =>
    if ltb n x && leb x m then None
    else Some (match_natlist l x t)
  | t1 |--> t2 =>
    match subst_type_opt l t1 n m , subst_type_opt l t2 n m with
    | Some ty1, Some ty2 => Some (ty1 |--> ty2)
    | _, _ => None
    end
  end.

Fixpoint opt_subst_type_list σ Γ n m :=
  match Γ with
  | nil => Some nil
  | h :: t =>
    match subst_type_opt σ h n m with
    | Some h' =>
      match opt_subst_type_list σ t n m with
      | Some t' => Some (h' :: t')
      | None => None
      end
    | None => None
    end
  end.

Fixpoint opt_subst_type_term σ e n m :=
  match e with
  | Abs x typ e1 =>
    match subst_type_opt σ typ n m, opt_subst_type_term σ e1 n m with
    | Some ty', Some e' => Some (Abs x ty' e')
    | _, _ => None
    end
  | App e1 e2 =>
    match opt_subst_type_term σ e1 n m, opt_subst_type_term σ e2 n m with
    | Some e1', Some e2' => Some (App e1' e2')
    | _, _ => None
    end
  | If e1 e2 e3 =>
    match opt_subst_type_term σ e1 n m, opt_subst_type_term σ e2 n m, opt_subst_type_term σ e3 n m with
    | Some e1', Some e2', Some e3' => Some (If e1' e2' e3')
    | _, _, _ => None
    end
  | _ => Some e
  end.

Lemma subst_type_opt_refl : forall σ typ n,
    subst_type_opt σ typ n n = Some (subst_type σ typ).
Proof.
  induction typ; simpl; intros; auto.
  -
    rewrite IHtyp1, IHtyp2. reflexivity.
  -
    destruct ltb eqn:IH1; simpl; auto.
    apply ltb_lt in IH1. apply leb_gt in IH1. rewrite IH1. reflexivity.
Qed.    

Lemma opt_subst_type_term_refl : forall σ e n,
    opt_subst_type_term σ e n n = Some (subst_type_term σ e).
Proof.
  induction e; simpl; intros; eauto.
  -
    rewrite IHe. rewrite subst_type_opt_refl. reflexivity.
  -
    rewrite IHe1, IHe2. reflexivity.
  -
    rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.    

Lemma opt_subst_type_list_refl : forall σ Γ n,
    opt_subst_type_list σ Γ n n = Some (subst_type_list σ Γ).
Proof.
  induction Γ; simpl; intros; auto.
  rewrite IHΓ. rewrite subst_type_opt_refl. reflexivity.
Qed.

Lemma opt_to_subst_type : forall typ σ n m t',
    subst_type_opt σ typ n m = Some t' ->
    subst_type σ typ = t'.
Proof.
  induction typ; simpl; intros; auto.
  -
    inversion H; subst; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    apply IHtyp1 in IH1. 
    destruct subst_type_opt eqn:IH2; try discriminate.
    apply IHtyp2 in IH2.
    inversion H; subst.
    reflexivity.
  -
    destruct ltb; simpl in H.
    destruct leb; try discriminate.
    inversion H; subst. reflexivity.
    inversion H; subst. reflexivity.
Qed.

Lemma opt_to_subst_list : forall l σ n m l',
    opt_subst_type_list σ l n m = Some l' ->
    subst_type_list σ l = l'.
Proof.
  induction l; simpl; intros; auto.
  -
    inversion H; subst. reflexivity.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    destruct opt_subst_type_list eqn:IH2; try discriminate.
    apply opt_to_subst_type in IH1.
    inversion H; subst.
    apply IHl in IH2. rewrite IH2.
    reflexivity.
Qed.    

Lemma opt_to_subst_term : forall e σ n m e',
    opt_subst_type_term σ e n m = Some e' ->
    subst_type_term σ e = e'.
Proof.
  induction e; simpl; intros; try solve [inversion H; subst; reflexivity].
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    apply opt_to_subst_type in IH1.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    apply IHe in IH2. inversion H; subst.
    reflexivity.
  -
    destruct opt_subst_type_term eqn:IH1; try discriminate.
    apply IHe1 in IH1.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    apply IHe2 in IH2.
    inversion H; subst. reflexivity.
  -
    destruct opt_subst_type_term eqn:IH1; try discriminate.
    apply IHe1 in IH1.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    apply IHe2 in IH2.
    destruct opt_subst_type_term eqn:IH3; try discriminate.
    apply IHe3 in IH3.
    inversion H; subst; reflexivity.
Qed.    

Lemma create_sigma_app : forall l1 n n1 m l2 s1 s2,
    create_sigma n n1 l1 = Some s1 ->
    create_sigma (n + n1) m l2 = Some s2 ->
    create_sigma n (n1 + m) (l1 ++ l2) = Some (s1 ++ s2).
Proof.
  induction l1; simpl; intros.
  -
    destruct n1; try discriminate.
    simpl in H. inversion H; subst. simpl.
    rewrite add_0_r in H0.
    apply H0.
  -
    destruct n1; try discriminate.
    simpl in H. destruct create_sigma eqn:IH; try discriminate.
    simpl. 
    inversion H; subst.
    erewrite IHl1; eauto. reflexivity.
    simpl.
    rewrite add_succ_r in H0.
    apply H0.
Qed.    

Lemma create_dom_le : forall m n x l σ,
    create_sigma n m l = Some σ ->
    x <= n ->
    dom_sigma_in x σ = false.
Proof.
  induction m; simpl; intros.
  -
    destruct l; try discriminate.
    inversion H; subst. reflexivity.
  -
    destruct l; try discriminate.
    destruct create_sigma eqn:IH; try discriminate.
    inversion H; subst.
    apply IHm with (x:= x) in IH; auto.
    simpl.
    destruct eqb eqn:IH0; auto.
    apply eqb_eq in IH0; subst.
    apply nle_succ_diag_l in H0.
    inversion H0.
Qed.

Lemma create_dom_lt : forall m n x l σ,
    create_sigma n m l = Some σ ->
    (n + m) < x ->
    dom_sigma_in x σ = false.
Proof.
  induction m; simpl; intros.
  -
    destruct l; try discriminate.
    inversion H; subst. reflexivity.
  -
    destruct l; try discriminate.
    destruct create_sigma eqn:IH; try discriminate.
    inversion H; subst.
    apply IHm with (x:= x) in IH; auto.
    simpl.
    destruct eqb eqn:IH0; auto.
    apply eqb_eq in IH0; subst.
    rewrite add_succ_r in H0.
    unfold Peano.lt in H0. apply le_S_n in H0.
    apply le_trans with (n:= S n) in H0.
    apply nle_succ_diag_l in H0. inversion H0.
    apply le_n_S. apply le_add_r.
    rewrite add_succ_r in H0. apply H0.
Qed.    

Lemma dom_notin_app : forall σ1 σ2 n,
    dom_sigma_in n σ1 = false ->
    dom_sigma_in n σ2 = false ->
    dom_sigma_in n (σ1 ++ σ2) = false.
Proof.
  induction σ1; simpl; intros; auto.
  destruct a. destruct eqb; try discriminate.
  apply IHσ1; auto.
Qed.

Lemma dom_notin_app_eq : forall ad n σ,
    dom_sigma_in n ad = false ->
    match_natlist σ n (TyVar n) = match_natlist (ad ++ σ) n (TyVar n).
Proof.
  induction ad; simpl; intros.
  -
    reflexivity.
  -
    destruct a. destruct eqb eqn:IH; try discriminate.
    apply IHad with (σ := σ) in H; eauto.
    rewrite eqb_sym. rewrite IH. rewrite H. reflexivity.
Qed.


Lemma opt_subst_type_dom_notin : forall typ σ n m T addty l,
    subst_type_opt σ typ n m = Some T ->
    (create_sigma n (m - n) l) = Some addty ->
    subst_type ( addty ++ σ ) typ = T.
Proof.
  induction typ; simpl; intros; auto.
  -
    inversion H; subst. reflexivity.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    destruct (subst_type_opt σ typ2) eqn:IH2; try discriminate.
    inversion H; subst.
    eapply IHtyp1 in IH1; eauto.
    eapply IHtyp2 in IH2; eauto.
    rewrite IH1, IH2. reflexivity.
  -
    destruct ltb eqn:IH1.
    destruct leb eqn:IH2; try discriminate;
    simpl in H; inversion H; subst.
    +
      apply leb_gt in IH2. apply create_dom_lt with (x:= n) in H0.
      apply dom_notin_app_eq with (σ := σ) in H0.
      symmetry. apply H0.
      destruct (leb n0 m) eqn:IH.
      apply leb_le in IH.
      rewrite add_sub_assoc; auto. rewrite add_comm.
      rewrite add_sub. apply IH2.
      apply leb_nle in IH.
      rewrite not_le_minus_0; auto. rewrite add_0_r.
      apply ltb_lt. apply IH1.
    +
      rewrite andb_false_l in H. inversion H; subst.
      apply ltb_ge in IH1.
      apply create_dom_le with (x:= n) in H0; auto.
      apply dom_notin_app_eq with (σ := σ) in H0.
      rewrite H0. reflexivity.
Qed.

Lemma opt_subst_list_dom_notin : forall l1 σ n m L addl l,
    opt_subst_type_list σ l1 n m = Some L ->
    (create_sigma n (m - n) l) = Some addl ->
    subst_type_list ( addl ++ σ ) l1 = L.
Proof.
  induction l1; simpl; intros; auto.
  -
    inversion H; subst. reflexivity.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    destruct opt_subst_type_list eqn:IH2; try discriminate.
    inversion H; subst. clear H.
    apply opt_subst_type_dom_notin with (addty:= addl) (l:= l) in IH1; auto.
    rewrite IH1.
    eapply IHl1 in IH2; eauto. rewrite IH2.
    reflexivity.
Qed.

Lemma opt_subst_term_dom_notin : forall e1 σ n m e addl l,
    opt_subst_type_term σ e1 n m = Some e ->
    (create_sigma n (m - n) l) = Some addl ->
    subst_type_term ( addl ++ σ ) e1 = e.
Proof.
  induction e1; simpl; intros; try solve[inversion H; subst; reflexivity].
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    inversion H; subst.
    eapply IHe1 in IH2; eauto. rewrite IH2.
    eapply opt_subst_type_dom_notin in IH1; eauto.
    rewrite IH1. reflexivity.
  -
    destruct opt_subst_type_term eqn:IH1; try discriminate.
    eapply IHe1_1 in IH1; eauto.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    eapply IHe1_2 in IH2; eauto.
    inversion H; subst. reflexivity.
  -
    destruct opt_subst_type_term eqn:IH1; try discriminate.
    eapply IHe1_1 in IH1; eauto.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    eapply IHe1_2 in IH2; eauto.
    destruct opt_subst_type_term eqn:IH3; try discriminate.
    eapply IHe1_3 in IH3; eauto.
    inversion H; subst. reflexivity.
Qed.

Lemma opt_subst_type_add : forall typ σ n m T addty l,
    subst_type_opt σ typ n m = Some T ->
    (create_sigma n (m - n) l) = Some addty ->
    subst_type_opt ( addty ++ σ ) typ n m = Some T.
Proof.
  induction typ; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    destruct (subst_type_opt σ typ2) eqn:IH2; try discriminate.
    inversion H; subst.
    eapply IHtyp1 in IH1; eauto.
    eapply IHtyp2 in IH2; eauto.
    rewrite IH1, IH2. reflexivity.
  -
    destruct ltb eqn:IH1.
    destruct leb eqn:IH2; try discriminate;
    simpl in H; inversion H; subst.
    +
      simpl.
      apply leb_gt in IH2. apply create_dom_lt with (x:= n) in H0.
      apply dom_notin_app_eq with (σ := σ) in H0. 
      symmetry. rewrite H0. reflexivity.
      apply ltb_lt in IH1.
      destruct (leb m n0) eqn:IH.
      apply leb_le in IH. apply sub_0_le in IH. rewrite IH. rewrite add_0_r.
      apply IH1.
      apply leb_gt in IH. apply lt_le_incl in IH.
      rewrite add_sub_assoc; auto. rewrite minus_plus.
      apply IH2.
    +
      rewrite andb_false_l in H. rewrite andb_false_l.
      inversion H; subst.
      apply ltb_ge in IH1.
      apply create_dom_le with (x:= n) in H0; auto.
      apply dom_notin_app_eq with (σ := σ) in H0.
      rewrite H0. reflexivity.
Qed.

Lemma opt_subst_list_add : forall l1 σ n m L addl l,
    opt_subst_type_list σ l1 n m = Some L ->
    (create_sigma n (m - n) l) = Some addl ->
    opt_subst_type_list ( addl ++ σ ) l1 n m = Some L.
Proof.
  induction l1; simpl; intros; auto.
  destruct subst_type_opt eqn:IH1; try discriminate.
  destruct opt_subst_type_list eqn:IH2; try discriminate.
  inversion H; subst. clear H.
  apply opt_subst_type_add with (addty:= addl) (l:= l) in IH1; auto.
  rewrite IH1.
  eapply IHl1 in IH2; eauto. rewrite IH2.
  reflexivity.
Qed.

Lemma opt_subst_term_add : forall e1 σ n m e addl l,
    opt_subst_type_term σ e1 n m = Some e ->
    (create_sigma n (m - n) l) = Some addl ->
    opt_subst_type_term ( addl ++ σ ) e1 n m = Some e.
Proof.
  induction e1; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH; try discriminate.
    erewrite opt_subst_type_add; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1; eauto; clear IH.
  -
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1_1; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1_2; eauto; clear IH.
  -
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1_1; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1_2; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1_3; eauto; clear IH.
Qed.    

Lemma opt_subst_type_add_range : forall typ σ n m T addty l x y,
    subst_type_opt σ typ n m = Some T ->
    n <= x -> y <= m ->
    (create_sigma x (y - x) l) = Some addty ->
    subst_type_opt ( addty ++ σ ) typ n m = Some T.
Proof.
  induction typ; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    apply IHtyp1 with (x:= x) (y:= y) (l:= l) (addty:= addty) in IH1; auto.
    destruct (subst_type_opt σ typ2) eqn:IH2; try discriminate.
    apply IHtyp2 with (x:= x) (y:= y) (l:= l) (addty:= addty) in IH2; auto.
    inversion H; subst.
    rewrite IH1, IH2. reflexivity.
  -
    destruct ltb eqn:IH1.
    +
      destruct leb eqn:IH2; try discriminate. simpl in H. simpl.
      rewrite <- dom_notin_app_eq; auto.
      apply ltb_lt in IH1. apply leb_gt in IH2.
      destruct (leb n x) eqn:IH0.
      apply leb_le in IH0.
      apply create_dom_le with (x:= n) in H2; auto.
      apply leb_gt in IH0.
      apply create_dom_lt with (x:= n) in H2; auto.
      destruct (leb x y) eqn:IH.
      apply leb_le in IH.
      rewrite add_sub_assoc; auto.
      rewrite  minus_plus. apply le_lt_trans with m; auto.
      apply leb_gt in IH.
      apply lt_le_incl in IH.
      apply sub_0_le in IH. rewrite IH, add_0_r.
      apply IH0.
    +
      rewrite andb_false_l. rewrite andb_false_l in H.
      inversion H. rewrite H4.
      apply ltb_ge in IH1.
      apply create_dom_le with (x:= n) in H2; auto.
      rewrite <- dom_notin_app_eq; auto.
      apply le_trans with n0; auto.
Qed.      
    
Lemma opt_subst_list_add_range : forall l1 σ n m l addL L x y,
    opt_subst_type_list σ l1 n m = Some L ->
    n <= x -> y <= m ->
    (create_sigma x (y - x) l) = Some addL ->
    opt_subst_type_list ( addL ++ σ ) l1 n m = Some L.
Proof.
  induction l1; simpl; intros; auto.
  destruct subst_type_opt eqn:IH1; try discriminate.
  destruct opt_subst_type_list eqn:IH2; try discriminate.
  inversion H; subst; clear H.
  erewrite opt_subst_type_add_range; eauto.
  erewrite IHl1; eauto.
Qed.

Lemma subst_type_opt_m : forall ty1 n m x σ ty2,
    x <= m ->
    subst_type_opt σ ty1 n m = Some ty2 ->
    subst_type_opt σ ty1 n x = Some ty2.
Proof.
  induction ty1; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    eapply IHty1_1 in IH1; eauto.
    destruct subst_type_opt eqn:IH2; try discriminate.
    eapply IHty1_2 in IH2; eauto.
    inversion H0; inversion IH1; inversion IH2; subst.
    rewrite IH1, IH2. reflexivity.
  -
    destruct ltb eqn:IH1; destruct leb eqn:IH2; try discriminate;
      simpl in H0; inversion H0; subst; try rewrite andb_false_l; auto.
    apply ltb_lt in IH1. apply leb_gt in IH2.
    apply le_lt_trans with (p:= n) in H; auto.
    apply leb_gt in H. rewrite H. simpl. reflexivity.
Qed.

Lemma opt_subst_type_list_m : forall l n m x σ l',
    x <= m ->
    opt_subst_type_list σ l n m = Some l' ->
    opt_subst_type_list σ l n x = Some l'.
Proof.
  induction l; simpl; auto; intros.
  destruct subst_type_opt eqn:IH1; try discriminate.
  eapply subst_type_opt_m in IH1; eauto. rewrite IH1.
  destruct opt_subst_type_list eqn:IH2; try discriminate.
  eapply IHl in IH2; eauto. rewrite IH2.
  apply H0.
Qed.

Lemma opt_subst_type_term_m : forall e n m x σ e',
    x <= m ->
    opt_subst_type_term σ e n m = Some e' ->
    opt_subst_type_term σ e n x = Some e'.
Proof.
  induction e; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    erewrite subst_type_opt_m; eauto.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    erewrite IHe; eauto.
  -
    destruct opt_subst_type_term eqn:IH1; try discriminate.
    erewrite IHe1; eauto; clear IH1.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe2; eauto.
  -
    destruct opt_subst_type_term eqn:IH1; try discriminate.
    erewrite IHe1; eauto; clear IH1.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe2; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe3; eauto; clear IH.
Qed.

Lemma subst_type_opt_n : forall ty1 n m x σ ty2,
    n <= x <= m ->
    subst_type_opt σ ty1 n m = Some ty2 ->
    subst_type_opt σ ty1 x m = Some ty2.
Proof.
  induction ty1; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    eapply IHty1_1 in IH1; eauto.
    destruct subst_type_opt eqn:IH2; try discriminate.
    eapply IHty1_2 in IH2; eauto.
    inversion H0; inversion IH1; inversion IH2; subst.
    rewrite IH1, IH2. reflexivity.
  -
    destruct ltb eqn:IH1.
    +
      destruct leb eqn:IH2; try discriminate.
      simpl in H0. inversion H0; subst.
      apply ltb_lt in IH1. apply leb_gt in IH2.
      destruct H.
      apply le_lt_trans with (p:= n) in H1; auto. apply ltb_lt in H1.
      rewrite H1. simpl. reflexivity.
    +
      rewrite andb_false_l in H0. inversion H0; subst.
      destruct H. apply ltb_ge in IH1.
      apply le_trans with (p:= x) in IH1; auto.
      apply ltb_ge in IH1. rewrite IH1.
      rewrite andb_false_l. reflexivity.
Qed.

Lemma subst_list_opt_n : forall l n m x σ l0,
    n <= x <= m ->
    opt_subst_type_list σ l n m = Some l0 ->
    opt_subst_type_list σ l x m = Some l0.
Proof.
  induction l; simpl; intros; auto.
  destruct subst_type_opt eqn:IH1; try discriminate.
  destruct opt_subst_type_list eqn:IH2; try discriminate.
  eapply subst_type_opt_n in IH1; eauto. rewrite IH1.
  eapply IHl in IH2; eauto. rewrite IH2.
  inversion H; subst; auto.
Qed.    

Lemma subst_term_opt_n : forall e n m x σ e0,
    n <= x <= m ->
    opt_subst_type_term σ e n m = Some e0 ->
    opt_subst_type_term σ e x m = Some e0.
Proof.
  induction e; simpl; intros; auto.
  -
    destruct subst_type_opt eqn:IH1; try discriminate.
    erewrite subst_type_opt_n; eauto.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    erewrite IHe; eauto.
  -
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe2; eauto; clear IH.
  -
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe1; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe2; eauto; clear IH.
    destruct opt_subst_type_term eqn:IH; try discriminate.
    erewrite IHe3; eauto; clear IH.
Qed.

Lemma create_sigma_in : forall y l1 x σ n,
    x < n <= (x + y) ->
    create_sigma x y l1 = Some σ ->
    dom_sigma_in n σ = true.
Proof.
  induction y; simpl; intros; destruct H.
  -
    rewrite add_0_r in H1.
    apply le_not_lt in H1. apply H1 in H. inversion H.
  -
    destruct l1; simpl in H0; try discriminate.
    destruct create_sigma eqn:IH; try discriminate.
    inversion H0; subst.
    simpl.
    destruct eqb eqn:IH0; auto.
    eapply IHy with (x:= S x); eauto.
    split. compute in H. apply eqb_neq in IH0.
    apply le_lteq in H. destruct H; auto.
    rewrite H in IH0. induction IH0. reflexivity.
    simpl. rewrite add_succ_r in H1. apply H1.
Qed.    

Lemma dom_in_app : forall σ1 σ2 n typ,
    dom_sigma_in n σ1 = true ->
    match_natlist (σ1 ++ σ2) n typ = match_natlist σ1 n typ.
Proof.
  induction σ1; simpl; intros; auto.
  -
    inversion H; subst.
  -
    destruct a. rewrite eqb_sym. destruct eqb; auto.
Qed.

Lemma subst_type_create_swap : forall ty1 l1 add1 l2 add2 x y z σ,
    x <= y <= z ->
    create_sigma x (y - x) l1 = Some add1 ->
    create_sigma y (z - y) l2 = Some add2 ->
    subst_type (add1 ++ add2 ++ σ) ty1 = subst_type (add2 ++ add1 ++ σ) ty1.
Proof.
  induction ty1; simpl; intros; auto.
  -
   erewrite IHty1_1, IHty1_2; eauto.
  -
    destruct H.
    destruct (n <=? x) eqn:IH1.
    +
      apply leb_le in IH1.
      apply create_dom_le with (x:=n) in H0; auto.
      apply create_dom_le with (x:= n) in H1; auto. generalize H0; intros.
      eapply dom_notin_app with (σ1:= add1) (σ2:= add2) in H0; eauto.
      eapply dom_notin_app with (σ1:= add2) (σ2:= add1) in H3; eauto.
      rewrite <- app_assoc_reverse.
      rewrite <- dom_notin_app_eq with (ad := add1 ++ add2); auto.
      rewrite <- app_assoc_reverse.
      rewrite <- dom_notin_app_eq with (ad := add2 ++ add1); auto.
      apply le_trans with x; auto.
    +
      apply leb_gt in IH1.
      destruct (leb n y) eqn:IH2.
      *
        apply leb_le in IH2.
        apply create_dom_le with (x:= n) in H1; auto.
        rewrite <- dom_notin_app_eq with (ad := add2); auto.
        apply create_sigma_in with (n:= n) in H0.
        generalize H0; intros.
        apply dom_in_app with (σ2:= (add2 ++ σ)) (typ:= (TyVar n)) in H0.
        apply dom_in_app with (σ2:= (σ)) (typ:= (TyVar n)) in H3. rewrite H3.
        rewrite H0. reflexivity.
        split; auto.
        rewrite add_sub_assoc; auto. rewrite minus_plus.
        apply IH2.
      *
        apply leb_gt in IH2.
        apply create_dom_lt with (x:= n) in H0; auto.
        destruct (n <=? z) eqn:IH3.
        **
          apply leb_le in IH3.
          apply create_sigma_in with (n:= n) in H1; auto.
          rewrite <- app_assoc_reverse.
          rewrite <- app_assoc.
          rewrite <- dom_notin_app_eq with (ad := add1); auto.
          rewrite dom_in_app with (σ2:= (add1 ++ σ)) (typ:= (TyVar n)); auto.
          apply dom_in_app with (σ2:= (σ)) (typ:= (TyVar n)); auto.
          split; auto.
          rewrite add_sub_assoc; auto.
          rewrite minus_plus. apply IH3.
        **
          apply leb_gt in IH3.
          apply create_dom_lt with (x:=n) in H1; auto.
          rewrite <- dom_notin_app_eq with (ad := add1); auto.
          repeat rewrite <- dom_notin_app_eq with (ad := add2); auto.
          rewrite <- dom_notin_app_eq with (ad := add1); auto.
          rewrite add_sub_assoc; auto.
          rewrite minus_plus. apply IH3.
        **
          rewrite add_sub_assoc; auto.
          rewrite minus_plus. apply IH2.
Qed.          

Theorem T22_3_7 : forall e Γ S1 C σ T n m Γ' e',
    opt_subst_type_list σ Γ n m = Some Γ' ->
    opt_subst_type_term σ e n m = Some e' ->
    Γ' |- e' \in T ->
    Γ |-- n ` e \in S1 | m ` C ->
    (forall x, n < x <= m -> dom_sigma_in x σ = false) ->
    exists l l', create_sigma n (m - n) l = Some l' /\
    subst_type (l' ++ σ) S1 = T /\ Constrais_sol_bool (l' ++ σ) C = true.
Proof.
  intros. generalize dependent T. generalize dependent σ.
  generalize dependent Γ'. generalize dependent e'.
  induction H2; intros.
  -
    simpl in H1.
    inversion H1; subst.
    inversion H2; subst.
    exists nil, nil. simpl. split; auto.
    rewrite sub_diag. simpl. reflexivity.
    split.
    rewrite opt_subst_type_list_refl in H0. inversion H0; subst.
    eapply getbind_sub in H; eauto.
    reflexivity.
  -
    simpl in H0.
    destruct subst_type_opt eqn:IH1; try discriminate.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    inversion H0; subst. clear H0. inversion H1; subst; clear H1.
    eapply IHConstrait_Type in H8; simpl; eauto.
    destruct H8. destruct H0. destruct H0. destruct H1.
    exists x0. exists x1. split; try split; auto.
    rewrite H1.
    eapply opt_subst_type_dom_notin in H0; eauto. rewrite H0.
    reflexivity.
    rewrite IH1. rewrite H. reflexivity.
  -
    simpl in H0.
    destruct opt_subst_type_list eqn:IH1; try discriminate.
    destruct opt_subst_type_term eqn:IH2; try discriminate.
    destruct (opt_subst_type_term σ t2) eqn:IH3; try discriminate.
    inversion H0; subst. clear H0.
    inversion H1; subst.
    eapply IHConstrait_Type1 with (σ := σ) in H5; eauto.
    destruct H5. destruct H0. destruct H0. destruct H2.
    eapply IHConstrait_Type2 with (σ := σ) in H7; eauto.
    clear IHConstrait_Type1; clear IHConstrait_Type2.
    destruct H7. destruct H5. destruct H5. destruct H6.
    +
      exists (x ++ x1 ++ [T]). exists (x0 ++ x2 ++ [( S F'', T)] ).
      split; try split; auto.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      apply create_sigma_app with (m := F'' - F') (l2 := x1) (s2 := x2) in H0; auto.
      rewrite add_sub_assoc in H0; auto.
      rewrite <- add_sub_swap in H0; auto.
      generalize (le_trans _ _ _ H2_ H2_0). intros.
      rewrite <- add_sub_assoc in H0; auto.
      rewrite minus_plus in H0.
      assert (create_sigma F'' (1) [T] =Some [(S F'', T)]).
      reflexivity.
      apply create_sigma_app with (m:= 1) (l2:= [T]) (s2:= [(S F'', T)]) in H0; auto.
      rewrite add_1_r in H0. rewrite <- add_1_l in H0. rewrite <- add_1_l.
      rewrite add_sub_assoc in H0; auto.
      rewrite app_assoc. rewrite app_assoc. apply H0.
      rewrite add_sub_assoc; auto. rewrite minus_plus. apply H9.
      rewrite <- le_plus_minus; auto. simpl.
      apply create_dom_lt with (x:= S F'') in H0.
      apply create_dom_lt with (x:= S F'') in H5.
      apply dom_notin_app with (σ2:= x2) in H0; eauto.
      apply dom_notin_app_eq with (σ := [(S F'', T)] ++ σ) in H0.
      simpl in H0. rewrite eqb_refl in H0.
      rewrite <- app_assoc in H0.
      repeat rewrite <- app_assoc.
      simpl. rewrite <- H0. reflexivity.
      apply CT_n_lt in H2_, H2_0.
      rewrite add_sub_assoc; auto. rewrite minus_plus; auto.
      apply CT_n_lt in H2_, H2_0.
      rewrite add_sub_assoc; auto. rewrite minus_plus; auto.
      apply le_lt_trans with F''; auto.
      admit.
    +
      clear IHConstrait_Type1; clear IHConstrait_Type2.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      inversion H; subst; clear H.
      apply subst_list_opt_n with F; auto.
      apply opt_subst_type_list_m with (S F''); auto.
    +
      clear IHConstrait_Type1; clear IHConstrait_Type2.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      inversion H; subst; clear H.
      apply opt_subst_type_term_m with (S F''); auto.
      apply subst_term_opt_n with F; auto.
    +
      clear IHConstrait_Type1; clear IHConstrait_Type2.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      inversion H; subst; clear H.
      intros. apply H3.
      destruct H.
      split; auto. apply le_lt_trans with F'; auto.
    +
      clear IHConstrait_Type1; clear IHConstrait_Type2.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      inversion H; subst; clear H.
      apply opt_subst_type_list_m with (S F''); eauto.
    +
      clear IHConstrait_Type1; clear IHConstrait_Type2.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      inversion H; subst; clear H.
      apply opt_subst_type_term_m with (S F''); eauto.
    +
      clear IHConstrait_Type1; clear IHConstrait_Type2.
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0.
      inversion H; subst; clear H.
      intros. apply H3.
      destruct H. split; auto.
      apply le_trans with F'; auto.
  -
    simpl in H0. inversion H0; subst. inversion H1; subst. exists [], [].
    simpl. rewrite sub_diag. simpl. split; auto.
  -
    simpl in H0. inversion H0; subst. inversion H1; subst. exists [], [].
    simpl. rewrite sub_diag. simpl. split; auto.
  -
    simpl in H0.
    destruct opt_subst_type_list eqn:IH1; try discriminate.

    destruct opt_subst_type_term eqn:IH2; try discriminate.
    destruct (opt_subst_type_term σ e2) eqn:IH3; try discriminate.
    destruct (opt_subst_type_term σ e3) eqn:IH4; try discriminate.
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    eapply IHConstrait_Type1 with (σ := σ) in H6; auto; clear IHConstrait_Type1.
    destruct H6. destruct H0. destruct H0. destruct H1.
    eapply IHConstrait_Type2 with (σ := σ) in H8; auto; clear IHConstrait_Type2.
    destruct H8. destruct H4. destruct H4. destruct H5.
    eapply IHConstrait_Type3 with (σ := σ) in H9; auto; clear IHConstrait_Type3.
    destruct H9. destruct H7. destruct H7. destruct H8.
    +
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0. apply CT_n_lt in H2_1.
      exists (x ++ x1 ++ x3). exists (x0 ++ x2 ++ x4). repeat split.
      ++
        apply create_sigma_app with (m:= F2 - F1) (l2:= x1) (s2:= x2) in H0.
        apply create_sigma_app with (m:= F3 - F2) (l2:= x3) (s2:= x4) in H0.
      *
        repeat rewrite <- app_assoc in H0.
        rewrite <- H0.
        rewrite <- add_sub_swap; auto.
        rewrite add_sub_assoc; auto.
        rewrite add_sub_assoc; auto.
        rewrite minus_plus.
        rewrite <- add_sub_assoc; auto.
        rewrite <- add_sub_swap; auto.
        rewrite add_sub_assoc; auto.
        rewrite minus_plus. reflexivity.
        apply le_trans with F1; auto.
      *
        rewrite <- H7.
        rewrite <- add_sub_swap; auto.
        rewrite add_sub_assoc; auto.
        rewrite minus_plus.
        rewrite add_sub_assoc; auto.
        rewrite minus_plus. reflexivity.
        apply le_trans with F1; auto.
        apply le_add_r.
      *
        rewrite <- H4.
        rewrite add_sub_assoc; auto.
        rewrite minus_plus. reflexivity.
      ++
        admit.
      ++
        admit.
    +
      apply CT_n_lt in H2_. apply CT_n_lt in H2_0. apply CT_n_lt in H2_1.
      inversion H; subst; clear H; clear H0.
      apply subst_list_opt_n with F; auto.
      split; auto. apply le_trans with F1; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      apply subst_term_opt_n with F; auto.
      split; auto. apply le_trans with F1; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      intros. apply H3.
      destruct H7. split; auto.
      apply le_lt_trans with F2; auto.
      apply le_trans with F1; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      inversion H; subst; clear H; clear H0.
      apply subst_list_opt_n with F; auto.
      apply opt_subst_type_list_m with F3; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      apply subst_term_opt_n with F; auto.
      apply opt_subst_type_term_m with F3; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      intros. apply H3.
      destruct H4. split; auto.
      apply le_lt_trans with F1; auto.
      apply le_trans with F2; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      inversion H; subst; clear H.
      apply opt_subst_type_list_m with F3; auto.
      apply le_trans with F2; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      inversion H; subst; clear H.
      apply opt_subst_type_term_m with F3; auto.
      apply le_trans with F2; auto.
    +
      apply CT_n_lt in H2_;apply CT_n_lt in H2_0; apply CT_n_lt in H2_1.
      intros. destruct H0.
      apply H3. split; auto.
      apply le_trans with F1; auto.
      apply le_trans with F2; auto.
Abort.
