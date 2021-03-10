Load "../std".
Import Nat.

Definition tyid := nat.

Inductive type : Set :=
| tyvar : tyid -> type
| arrow : type -> type -> type
| Π : type -> type.

Inductive exp : Set :=
| var : nat -> exp
| abs : type -> exp -> exp
| app : exp -> exp -> exp
| Λ : exp -> exp
| tapp : exp -> type -> exp.

Definition isval e :=
  match e with
  | abs _ _ => true
  | Λ _ => true
  | _ => false
  end.

Definition context := (list type).

Fixpoint shift_type d c ty :=
  match ty with
  | tyvar n => tyvar (if c <=? n then (n + d) else n)
  | arrow ty1 ty2 => arrow (shift_type d c ty1) (shift_type d c ty2)
  | Π ty1 => Π (shift_type d (S c) ty1)
  end.

Fixpoint subst_type (d: nat) (ty1 ty2: type) :=
  match ty1 with
  | tyvar n =>
    if d =? n then shift_type d 0 ty2
    else if d <? n then tyvar (pred n) else (tyvar n)
  | arrow t1 t2 => arrow (subst_type d t1 ty2) (subst_type d t2 ty2)
  | Π t1 => Π (subst_type (S d) t1 ty2)
  end.

Fixpoint shift_ty_exp (d c: nat) (e: exp) :=
  match e with
  | var _ => e
  | app e1 e2 => app (shift_ty_exp d c e1) (shift_ty_exp d c e2)
  | abs ty e1 => abs (shift_type d c ty) (shift_ty_exp d c e1)
  | tapp e1 ty => tapp (shift_ty_exp d c e1) (shift_type d c ty)
  | Λ e1 => Λ (shift_ty_exp d (S c) e1)
  end.

Definition shift_list n m Γ := (map (shift_type n m) Γ).

Fixpoint subst_ty_exp (d: nat) (ty: type) (e: exp) : exp :=
  match e with
  | var _ => e
  | abs ty1 e1 => abs (subst_type d ty1 ty) (subst_ty_exp d ty e1)
  | app e1 e2 => app (subst_ty_exp d ty e1) (subst_ty_exp d ty e2)
  | Λ e1 => Λ (subst_ty_exp (S d) ty e1)
  | tapp e1 ty2 => tapp (subst_ty_exp d ty e1) (subst_type d ty2 ty)
  end.

Notation " [[ X |-->  T2 ]] t1 " := (subst_ty_exp X T2 t1) (at level 50).

Fixpoint shift_exp (d c : nat) (t : exp) :=
match t with
| var x => var (if c <=? x then x + d else x)
| abs ty e1 => abs (shift_type d c ty) (shift_exp d (S c) e1)
| app e1 e2 => app (shift_exp d c e1) (shift_exp d c e2)
| Λ e1 => Λ (shift_exp d c e1)
| tapp e1 ty1 => tapp (shift_exp d c e1) ty1
end.

Fixpoint subst_exp (d : nat) (s t: exp) : exp :=
match t with
| var x => if d =? x then shift_exp d 0 (shift_ty_exp d 0 s)
           else if d <? x then var (pred x)
                else var x
| abs ty e1 => abs ty (subst_exp (S d) s e1)
| app e1 e2 => app (subst_exp d s e1) (subst_exp d s e2)
| Λ e1 => Λ (subst_exp (S d) s e1)
| tapp e1 ty => tapp (subst_exp d s e1) ty
end.

Notation " [[ X \ t2 ]] t1 " := (subst_exp X t2 t1) (at level 50).

Fixpoint eval_exp e : option exp :=
  match e with
  | app e1 e2 =>
    match isval e1, isval e2 with
    | true, true =>
      match e1 with
      | abs _ t => Some ( [[0 \ e2]]t)
      | _ => None
      end
    | false, _ =>
      match eval_exp e1 with
      | Some e1' => Some (app e1' e2)
      | None => None
      end
    | _, false =>
      match eval_exp e2 with
      | Some e2' => Some (app e1 e2')
      | None => None
      end
    end
  | tapp (Λ e1) ty => Some ( [[ 0 |--> ty ]] e1 )
  | tapp e1 ty =>
    match eval_exp e1 with
    | Some e1' => Some (tapp e1' ty)
    | None => None
    end
  | _ => None
  end.

Fixpoint nth_opt {T: Type} (l: list T) (n: nat) : option T :=
  match n, l with
  | 0, (h:: t) => Some h
  | _, nil => None
  | (S m), (h:: t) => nth_opt t m
  end.

Fixpoint eqb_type ty1 ty2 :=
  match ty1, ty2 with
  | tyvar n1, tyvar n2 => n1 =? n2
  | arrow t1 t2, arrow t1' t2' => (eqb_type t1 t1') && (eqb_type t2 t2')
  | Π t1, Π t2 => eqb_type t1 t2
  | _, _ => false
  end.

Fixpoint type_of (Γ: context) (e: exp) : option type :=
  match e with
  | var n =>
    match nth_opt Γ n with
    | Some ty => Some ty
    | _ => None
    end
  | abs ty e1 =>
    match type_of (ty :: Γ) e1 with
    | Some ty2 => Some (arrow ty ty2)
    | None => None
    end
  | app e1 e2 =>
    match type_of Γ e1, type_of Γ e2 with
    | Some (arrow ty1 ty), Some ty2 =>
      if eqb_type ty1 ty2 then (Some ty) else None
    | _, _ => None
    end
  | Λ e1 =>
    match type_of (shift_list 1 0 Γ) e1 with
    | Some ty => Some (Π ty)
    | None => None
    end
  | tapp e1 T2 =>
    match type_of Γ e1 with
    | Some (Π ty1) => Some ( subst_type 0 ty1 T2)
    | _ => None
    end
  end.

Section exapmle.

Let e1 := (Λ (abs (tyvar 0) (var 0) )).
Compute (type_of [] e1).
Compute (eval_exp (tapp e1 (tyvar 1))).

End exapmle.


Inductive value : exp -> Prop :=
| AbsV : forall ty e, value (abs ty e)
| TAbsV : forall e, value (Λ e).

Reserved Notation "e1 --> e2" (at level 50).
Inductive onestep : exp -> exp -> Prop :=
| E_App1 : forall e1 e2 e,
    e1 --> e -> (app e1 e2) --> (app e e2)
| E_App2: forall v1 e2 e,
    value v1 -> e2 --> e -> (app v1 e2) --> (app v1 e)
| E_AppAbs : forall ty e1 v,
    value v -> (app (abs ty e1) v) --> [[ 0 \ v ]]e1
| E_TApp : forall e1 e2 ty,
    e1 --> e2 -> (tapp e1 ty) --> (tapp e2 ty)
| E_TAppAbs : forall e ty,
    (tapp (Λ e) ty) --> [[ 0 |--> ty]]e
where "e1 --> e2" := (onestep e1 e2).

Reserved Notation "Γ |- e \in ty" (at level 40).
Inductive has_type : context -> exp -> type -> Prop :=
| T_Var : forall n Γ ty,
    nth_opt Γ n = Some ty ->
    Γ |- (var n) \in ty
| T_Abs : forall Γ ty e T,
    (T :: Γ) |- e \in ty ->
    Γ |- (abs T e) \in (arrow T ty)
| T_App : forall e1 e2 Γ ty1 ty2,
    Γ |- e1 \in arrow ty1 ty2 ->
    Γ |- e2 \in ty1 ->
    Γ |- (app e1 e2) \in ty2
| T_TAbs : forall e ty Γ,
    (shift_list 1 0 Γ) |- e \in ty ->
    Γ |- Λ e \in Π ty
| T_TApp : forall Γ e1 ty1 ty2,
    Γ |- e1 \in Π ty1 ->
    Γ |- tapp e1 ty2 \in subst_type 0 ty1 ty2
where "Γ |- e \in ty " := (has_type Γ e ty).

Lemma isval_val : forall e,
    value e <-> isval e = true.
Proof.
  destruct e; split; simpl; intros; try solve_by_invert; auto; constructor.
Qed.

Lemma val_not_eval : forall e,
    value e -> not (exists e', e --> e').
Proof.
  repeat intro.
  destruct H0. destruct H; try solve_by_invert.
Qed.

Lemma eval_step : forall e1 e2,
    e1 --> e2 <-> eval_exp e1 = Some e2.
Proof.
  split; intros.
  -
    induction H; eauto.
    +
      simpl. destruct isval eqn:IH.
      apply isval_val in IH.
      apply val_not_eval in IH. induction IH.
      exists e; auto.
      rewrite IHonestep. reflexivity.
    +
      simpl. apply isval_val in H. rewrite H.
      destruct (isval e2) eqn:IH.
      apply isval_val in IH. apply val_not_eval in IH; induction IH; eauto.
      rewrite IHonestep. reflexivity.
    +
      simpl. rewrite isval_val in H; rewrite H. reflexivity.
    +
      simpl.
      destruct e1; try solve_by_invert;
      rewrite IHonestep; reflexivity.
  -
    generalize dependent e2; induction e1; simpl; intros; try discriminate; eauto.
    +
      destruct isval eqn:IH1. destruct (isval e1_2) eqn:IH2.
      destruct e1_1; try discriminate. inversion H; subst. constructor. apply isval_val; auto.
      destruct (eval_exp e1_2) eqn:IH3; try discriminate.
      inversion H; subst. constructor. apply isval_val; auto.
      apply IHe1_2. reflexivity.
      destruct (eval_exp e1_1) eqn:IH2; try discriminate.
      inversion H; subst; clear H.
      constructor; eauto.
    +
      destruct e1; try discriminate;
      destruct eval_exp eqn:IH; inversion H; subst;
        constructor; eauto.
Qed.

Lemma eqb_type_refl : forall ty,
    eqb_type ty ty = true.
Proof.
  induction ty; simpl; auto.
  rewrite Nat.eqb_refl. reflexivity.
  rewrite IHty1, IHty2; reflexivity.
Qed.

Lemma eqb_type_eq : forall ty1 ty2,
    ty1 = ty2 <-> eqb_type ty1 ty2 = true.
Proof.
  split; intros; try solve [subst; apply eqb_type_refl].
  generalize dependent ty2; induction ty1; simpl; intros; auto;
  destruct ty2; try discriminate.
  -
    destruct eqb eqn:IH; try discriminate. apply eqb_eq in IH. subst; reflexivity.
  -
    apply andb_prop in H. destruct H.
    apply IHty1_1 in H; apply IHty1_2 in H0; subst; reflexivity.
  -
    apply IHty1 in H; subst; reflexivity.
Qed.    

Lemma type_of_has : forall e Γ ty,
    Γ |- e \in ty <-> type_of Γ e = Some ty.
Proof.
  split; intros.
  -
    induction H; simpl; eauto.
    +
      rewrite H; reflexivity.
    +
      rewrite IHhas_type; reflexivity.
    +
      rewrite IHhas_type1, IHhas_type2.
      rewrite eqb_type_refl. reflexivity.
    +
      rewrite IHhas_type. reflexivity.
    +
      rewrite IHhas_type. reflexivity.
  -
    revert H. revert Γ. revert ty.
    induction e; simpl; intros.
    +
      constructor. destruct nth_opt eqn:IH; try discriminate; auto.
    +
      destruct type_of eqn:IH; try discriminate.
      inversion H; subst. constructor; eauto.
    +
      destruct type_of eqn:IH1; try discriminate.
      destruct t0; try discriminate. apply IHe1 in IH1.
      destruct type_of eqn:IH2; try discriminate.
      apply IHe2 in IH2. destruct eqb_type eqn:IH3; try discriminate.
      apply eqb_type_eq in IH3; inversion H; subst.
      econstructor; eauto.
    +
      destruct type_of eqn:IH; try discriminate.
      inversion H; subst. constructor; auto.
    +
      destruct type_of eqn:IH1; try discriminate.
      destruct t1; try discriminate.
      inversion H; subst. 
      econstructor; eauto.
Qed.

Theorem T22_5_2 : forall e ty,
    [] |- e \in ty ->
    value e \/ (exists e', e --> e').
Proof.
  induction e; intros; inversion H; subst; try solve [left; constructor]; right.
  -
    destruct n; try discriminate.
  -
    generalize H3; intros.
    apply IHe1 in H3. apply IHe2 in H5.
    destruct H3.
    destruct H5.
    inversion H1; subst; try solve_by_invert.
    exists ([[0 \ e2]]e); constructor; auto.
    destruct H2. exists (app e1 x); constructor; auto.
    destruct H1. exists (app x e2); constructor; auto.
  -
    generalize H4; intros.
    apply IHe in H0.
    destruct H0.
    inversion H0; subst; try solve_by_invert.
    exists ([[0 |--> t0]]e0); constructor.
    destruct H0. exists (tapp x t0); constructor; auto.
Qed.


Lemma shift_ty0 : forall ty n,
    shift_type 0 n ty = ty.
Proof.
  induction ty; simpl; intros; eauto.
  -
    destruct leb; auto.
  -
    rewrite IHty1, IHty2; reflexivity.
  -
    rewrite IHty; reflexivity.
Qed.    

Lemma shift_exp0 : forall e n,
    shift_exp 0 n e = e.
Proof.
  induction e; simpl; intros; auto.
  -
    destruct leb; auto.
  -
    rewrite IHe, shift_ty0; reflexivity.
  -
    rewrite IHe1, IHe2; reflexivity.
  -
    rewrite IHe; reflexivity.
  -
    rewrite IHe; reflexivity.
Qed.

Lemma appnth : forall (ctx ctx': context) n,
    nth_opt (ctx ++ ctx') (n + (length ctx)) = nth_opt ctx' n.
Proof.
  induction ctx; simpl; intros; auto.
  rewrite <- plus_Snm_nSm. simpl. apply IHctx.
Qed.

Lemma length1_Some : forall n (ctx ctx1 ctx2: context) T,
    n < length ctx ->
    nth_opt (ctx ++ ctx1) n = Some T ->
    nth_opt (ctx ++ ctx2) n = Some T.
Proof.
  induction n; simpl; intros. destruct ctx. inversion H. simpl. simpl in H0. apply H0.
  destruct ctx. inversion H. simpl. destruct ( (t0 :: ctx) ++ ctx1) eqn:IHH. inversion H0. inversion IHH; subst.
  eapply IHn in H0. apply H0. simpl in H. apply lt_S_n in H. apply H.
Qed.

Lemma nth_opt_Some_lt : forall {A: Type} n (Γ: list A) x,
    nth_opt Γ n = Some x -> n < length Γ.
Proof.
  induction n; simpl; intros.
  -
    destruct Γ; simpl in H.
    inversion H.
    inversion H; subst. simpl.
    apply lt_0_succ.
  -
    destruct Γ. inversion H.
    simpl in H.
    apply IHn in H.
    simpl. apply lt_n_S.
    apply H.
Qed.    

Lemma nth_opt_non_shift : forall Γ n m x,
    nth_opt Γ x = None ->
    nth_opt (map (shift_type n m) Γ) x = None.
Proof.
  induction Γ; simpl; intros.
  destruct x; auto.
  destruct x; try discriminate H.
  apply IHΓ. apply H.
Qed.

Lemma shift_map_gamma : forall Γ n m x Δ,
  nth_opt Γ x = nth_opt Δ x ->
  nth_opt (map (shift_type n m) Γ) x = nth_opt (map (shift_type n m) Δ) x.
Proof.
  induction Γ; intros.
  simpl in H. simpl.
  destruct Δ.
  destruct x; auto.
  destruct x; simpl in H; auto.
  inversion H. simpl.
  symmetry; apply nth_opt_non_shift. rewrite H. reflexivity.
  destruct x; simpl in H; simpl.
  destruct Δ; simpl in H; inversion H; subst.
  simpl. reflexivity.
  destruct Δ. simpl in H. simpl. 
  simpl.
  apply nth_opt_non_shift. apply H.
  simpl. simpl in H.
  apply IHΓ. apply H.
Qed.

Lemma weakend : forall Γ e ty Δ,
    (forall x, x < length Γ -> nth_opt Γ x = nth_opt Δ x) ->
    Γ |- e \in ty -> Δ |- e \in ty.
Proof.
  intros. generalize dependent Δ. induction H0; simpl; intros.
  -
    constructor.
    rewrite <- H0. apply H.
    apply nth_opt_Some_lt in H. apply H.
  -
    constructor. apply IHhas_type; intros.
    clear IHhas_type; clear H0.
    destruct x; simpl. reflexivity.
    apply H. apply lt_S_n. apply H1.
  -
    econstructor; eauto.
  -
    constructor. apply IHhas_type; intros.
    apply shift_map_gamma.
    apply H. unfold shift_list in H1; rewrite map_length in H1. apply H1.
  -
    econstructor; eauto.
Qed.

Lemma shift_type_range : forall ty c c1 d d1,
    c <= c1 <= c + d ->
    shift_type d1 c1 (shift_type d c ty) = shift_type (d1 + d) c ty.
Proof.
  induction ty; intros; eauto.
  -
    simpl. destruct H.
    destruct (c <=? t0) eqn:IH1. apply leb_le in IH1.
    assert (c1 <=? t0 + d = true).
    apply leb_le.
    apply le_trans with (c + d); auto.
    apply plus_le_compat_r. apply IH1.
    rewrite H1. rewrite (add_comm d1). rewrite add_assoc. reflexivity.
    apply leb_gt in IH1.
    assert (c1 <=? t0 = false).
    apply leb_gt.
    apply lt_le_trans with c; auto.
    rewrite H1. reflexivity.
  -
    simpl. rewrite IHty1, IHty2; auto.
  -
    simpl. rewrite IHty; auto.
    destruct H.
    split; apply le_n_S; auto.
Qed.

Lemma shift_ty_exp_range : forall e c c1 d d1,
    c <= c1 <= c + d ->
    shift_ty_exp d1 c1 (shift_ty_exp d c e) = shift_ty_exp (d1 + d) c e.
Proof.
  induction e; simpl; intros; eauto.
  -
    rewrite IHe; auto.
    rewrite shift_type_range; auto.
  -
    rewrite IHe1, IHe2; auto.
  -
    rewrite IHe; auto.
    destruct H; split; apply le_n_S; auto.
  -
    rewrite IHe; auto.
    rewrite shift_type_range; auto.
Qed.    

Lemma shift_type_le : forall ty c c1 d d1,
    c1 <= c ->
    shift_type d1 c1 (shift_type d c ty) = shift_type d (d1 + c) (shift_type d1 c1 ty).
Proof.
  induction ty; simpl; intros; eauto.
  -
    destruct (leb c t0) eqn:IH1.
    apply leb_le in IH1.
    assert (leb c1 t0 = true).
    apply leb_le. apply le_trans with c; auto.
    rewrite H0. apply leb_le in H0.
    destruct (leb c1 (t0 + d)) eqn:IH2.
    apply leb_le in IH2.
    assert (leb (d1 + c) (t0 + d1) = true).
    apply leb_le. rewrite add_comm. apply plus_le_compat_r; auto.
    rewrite H1. rewrite <- add_assoc. rewrite (add_comm d d1). rewrite add_assoc. reflexivity.

    apply leb_gt in IH2.
    apply le_lt_trans with (n:= t0) in IH2; try apply le_add_r.
    apply le_not_lt in H0. induction H0; auto.

    apply leb_gt in IH1.
    destruct leb eqn:IH2.

    apply leb_le in IH2.
    assert (d1 + c <=? t0 + d1 = false).
    apply leb_gt. rewrite add_comm. apply plus_lt_compat_l. apply IH1.
    rewrite H0. reflexivity.

    apply leb_gt in IH2. apply lt_lt_add_l with (p:= d1) in IH1.
    apply leb_gt in IH1. rewrite IH1. reflexivity.
  -
    rewrite IHty1, IHty2; auto.
  -
    rewrite IHty; auto.
    rewrite add_succ_r. reflexivity.
    apply le_n_S; apply H.
Qed.

Lemma shift_ty_exp_le : forall e c c1 d d1,
    c1 <= c ->
    shift_ty_exp d1 c1 (shift_ty_exp d c e) = shift_ty_exp d (d1 + c) (shift_ty_exp d1 c1 e).
Proof.
  induction e; simpl; intros; auto.
  -
    rewrite IHe; auto.
    rewrite shift_type_le; auto.
  -
    rewrite IHe1, IHe2; auto.
  -
    rewrite IHe; auto.
    rewrite add_succ_r. reflexivity.
    apply le_n_S; apply H.
  -
    rewrite IHe; auto.
    rewrite shift_type_le; auto.
Qed.    

Lemma shift_list_swap : forall Γ n m,
    shift_list 1 0 (shift_list n m Γ)  = shift_list n (S m) (shift_list 1 0 Γ).
Proof.
  induction Γ; auto; intros.
  simpl. rewrite IHΓ.
  rewrite shift_type_le.
  rewrite add_1_l. reflexivity.
  apply Peano.le_0_n.
Qed.

Fixpoint subst_typen (d: nat) (ty1 ty2: type) :=
  match ty1 with
  | tyvar n =>
    if d =? n then ty2
    else if d <? n then tyvar (pred n) else (tyvar n)
  | arrow t1 t2 => arrow (subst_typen d t1 ty2) (subst_typen d t2 ty2)
  | Π t1 => Π (subst_typen (S d) t1 (shift_type 1 0 ty2))
  end.

Lemma subst_substn : forall ty1 ty2 n,
    subst_type n ty1 ty2 = subst_typen n ty1 (shift_type n 0 ty2).
Proof.
  induction ty1; simpl; intros.
  -
    reflexivity.
  -
    rewrite IHty1_1, IHty1_2; auto.
  -
    rewrite IHty1; auto.
    rewrite shift_type_range; auto.
    rewrite add_0_l; split; auto.
    apply le_0_n.
Qed.

Lemma shift_sub_cn : forall ty n c d ty1,
    c <= n ->
    shift_type d c (subst_type n ty ty1) =
       subst_type (n + d) (shift_type d c ty) ty1.
Proof.
  induction ty; simpl; intros; auto.
  -
    destruct eqb eqn:IH.
    +
      apply eqb_eq in IH; subst.
      apply leb_le in H. rewrite H.
      rewrite eqb_refl. rewrite shift_type_range; repeat split; auto.
      rewrite add_comm. reflexivity.
      apply le_0_n. rewrite add_0_l.
      apply leb_le; auto.
    +
      assert (n + d =? t0 + d = false ).
      {
        apply eqb_neq; intro.
        rewrite add_comm in H0.
        rewrite (add_comm t0) in H0.
        apply plus_reg_l in H0. subst.
        rewrite eqb_refl in IH. inversion IH.
      }
      destruct ltb eqn:IH1.
      ++
        apply ltb_lt in IH1.
        assert (c <=? t0 = true).
        { apply leb_le, lt_le_incl.
        apply le_lt_trans with n; auto. }
        rewrite H1.
        rewrite H0.
        destruct t0. inversion IH1.
        apply le_lt_trans with (p:= S t0) in H; auto.
        compute in H. apply le_S_n in H.
        apply plus_lt_compat_r with (p:=d) in IH1.
        apply ltb_lt in IH1. rewrite IH1. simpl. 
        apply leb_le in H. rewrite H. reflexivity.
      ++
        destruct leb eqn:IH2.
        +++
          rewrite H0.
          apply ltb_ge in IH1. apply plus_le_compat_r with (p:=d) in IH1.
          apply ltb_ge in IH1. rewrite IH1.
          simpl. rewrite IH2. reflexivity.
        +++
          simpl. rewrite IH2.
          apply ltb_ge in IH1. apply leb_gt in IH2.
          assert (n + d <? t0 = false).
          {
            apply ltb_ge. apply le_plus_trans; auto.
          }
          rewrite H1.
          assert (n + d =? t0 = false).
          {
            apply eqb_neq; intro.
            symmetry in H2; subst.
            destruct d.
            rewrite add_0_r in IH2.
            apply leb_gt in IH2. apply leb_nle in IH2.
            apply IH2; auto.
            apply le_add_le_sub_l in IH1.
            rewrite sub_diag in IH1.
            inversion IH1.
          }
          rewrite H2. reflexivity.
  -
    rewrite IHty1, IHty2; auto.
  -
    rewrite IHty; auto.
    apply le_n_S; auto.
Qed.

Lemma shift_sub_nc : forall ty n c d ty1,
    n <= c ->
    shift_type d c (subst_type n ty ty1) =
       subst_type n (shift_type d (S c) ty) (shift_type d (c - n) ty1).
Proof.
  induction ty; simpl; intros; auto.
  -
    destruct eqb eqn:IH.
    +
      apply eqb_eq in IH; subst.
      destruct t0; simpl.
      repeat rewrite shift_ty0. rewrite sub_0_r. reflexivity.
      assert (leb c t0 = false). apply leb_gt.
      apply lt_le_trans with (S t0); auto.
      rewrite H0. rewrite eqb_refl.
      rewrite (shift_type_le ty1 (c - S t0) 0 ); auto.
      assert (S t0 + (c - S t0) = c).
      { rewrite le_plus_minus_r. reflexivity. apply H. }
      rewrite H1. reflexivity.
      apply le_0_n.
    +
      destruct ltb eqn:IH0.
      ++
        apply ltb_lt in IH0.
        destruct t0. inversion IH0. simpl.
        destruct leb eqn:IH1; simpl.
        +++
          apply leb_le in IH1.
          apply lt_lt_add_r with (p:= d) in IH0.
          rewrite add_succ_l in IH0.
          apply ltb_lt in IH0. rewrite IH0.
          destruct (eqb n (S (t0 + d))) eqn:IH2.
          apply eqb_eq in IH2; subst.
          rewrite ltb_irrefl in IH0. discriminate IH0.
          reflexivity.
        +++
          apply leb_gt in IH1.
          destruct eqb eqn:IH2.
          apply eqb_eq in IH2; subst.
          induction (lt_irrefl (S t0)); auto.
          apply ltb_lt in IH0; rewrite IH0.
          reflexivity.
      ++
        apply ltb_ge in IH0.
        destruct t0; simpl. rewrite IH.
        destruct leb eqn:IH1; auto.
        apply leb_le in IH1. inversion IH1; subst.
        inversion H; subst. simpl in IH; discriminate IH.

        destruct leb eqn:IH1.
        +++
          apply leb_le in IH1.
          apply le_trans with (p:= S t0) in H; auto.
          apply le_lt_or_eq in IH0.
          destruct IH0; subst.
          apply le_not_lt in H. induction H; auto.
          rewrite eqb_refl in IH. discriminate IH.
        +++
          apply leb_gt in IH1.
          apply lt_lt_succ_r in IH1.
          apply lt_S_n in IH1.
          apply leb_gt in IH1.
          rewrite IH1. rewrite IH.
          apply ltb_ge in IH0.
          rewrite IH0. reflexivity.
  -
    rewrite IHty1, IHty2; auto.
  -
    rewrite IHty; auto.
    apply le_n_S; auto.
Qed.

Lemma shift_type_pre : forall e Γ ty n m,
    Γ |- e \in ty ->
    (shift_list n m Γ) |- (shift_ty_exp n m e) \in (shift_type n m ty).
Proof.
  intros. revert n; revert m.
  induction H; simpl; intros; try econstructor; eauto.
  -
    generalize dependent Γ.
    induction n; simpl; intros.
    destruct Γ; try discriminate; auto.
    simpl. simpl in H. inversion H; subst. reflexivity.
    destruct Γ; try discriminate.
    simpl. simpl in H. apply IHn. apply H.
  -
    rewrite shift_list_swap.
    apply IHhas_type.
  -
    rewrite shift_sub_nc.
    rewrite sub_0_r.
    econstructor. simpl in IHhas_type. apply IHhas_type.
    apply le_0_n.
Qed.

Lemma sub_shift_type : forall ty1 n (c: nat) d c ty2,
    c <= n -> S n <= d + c ->
    subst_type n (shift_type d c ty1) ty2
               = shift_type (pred d) c ty1.
Proof.
  induction ty1; simpl; intros.
  -
    destruct leb eqn:IH1.
    +
      apply leb_le in IH1.
      destruct d.

      rewrite add_0_l in H0.
      apply le_lt_n_Sm in H. apply lt_le_trans with (p:= c0) in H; auto.
      apply lt_irrefl in H. inversion H.

      rewrite add_succ_r. simpl.
      assert (n =? S (t0 + d) = false).
      {
        apply eqb_neq; intro. subst.
        apply plus_le_compat_l with (p:= S d) in IH1.
        apply le_trans with (p:= S d + t0) in H0; auto.
        rewrite add_comm in H0.
        apply nle_succ_diag_l in H0. apply H0.
      }
      rewrite H1.
      assert (n <? S (t0 + d) = true).
      {
        apply ltb_lt. rewrite add_succ_l in H0. apply le_S_n in H0.
        apply plus_le_compat_r with (p:= d) in IH1.
        apply le_lt_n_Sm.
        apply le_trans with (d + c0); auto.
        rewrite add_comm; apply IH1.
      }
      rewrite H2. reflexivity.
    +
      assert (n =? t0 = false).
      {
        apply eqb_neq; intro; subst.
        apply leb_nle in IH1. apply IH1.
        apply H.
      }
      rewrite H1.
      apply leb_gt in IH1.
      apply lt_le_trans with (p:= n) in IH1; auto.
      apply lt_le_incl in IH1.
      apply ltb_ge in IH1. rewrite IH1.
      reflexivity.
  -
    rewrite IHty1_1, IHty1_2; auto.
  -
    rewrite IHty1; auto.
    apply le_n_S. apply H.
    rewrite add_succ_r. apply le_n_S. apply H0.
Qed.

Lemma sub_type_pre : forall e Γ ty n T,
    Γ |- e \in ty ->
    (map (fun t' => subst_type n t' T) Γ) |- (subst_ty_exp n T e) \in subst_type n ty T.
Proof.
  intros. revert n; revert T.
  induction H; simpl; intros.
  -
    constructor.
    revert H; revert Γ.
    induction n; intros.
    destruct Γ; simpl in H. inversion H.
    inversion H; subst. simpl. reflexivity.
    destruct Γ; simpl in H. inversion H.
    apply IHn. apply H.
  -
    constructor.
    simpl in IHhas_type.
    apply IHhas_type.
  -
    econstructor; eauto.
  -
    constructor.
    assert (shift_list 1 0 (map (fun t' => subst_type n t' T) Γ) = map (fun t' => subst_type (S n) t' T) (shift_list 1 0 Γ)).
    {
      clear. revert n. revert T.
      induction Γ; simpl; intros; auto.
      rewrite IHΓ.
      rewrite shift_sub_cn. rewrite add_1_r. reflexivity.
      apply le_0_n.
    }
    rewrite H0. apply IHhas_type.
  -
    admit.
Abort.

Lemma shifting : forall e g g1 g2 T,
  (g1 ++ g) |- e \in T ->
  (g1 ++ g2 ++ g) |- (shift_exp (length g2) (length g1) e) \in T.
Proof.
  induction e; simpl; intros; inversion H; subst; try solve [econstructor; eauto].
  -
    apply T_Var. destruct leb eqn:IH. apply leb_le in IH.
    generalize dependent g. generalize dependent T. generalize dependent n.
    induction g1; simpl; intros; eauto. rewrite appnth. apply H2.
    destruct n. inversion IH. simpl.
    apply le_S_n in IH. eapply IHg1 in IH; eauto.
    constructor. apply H2.
    apply leb_gt in IH. eapply length1_Some in IH. apply IH. apply H2.
  -
    admit.
  -
    econstructor; eauto.
    unfold shift_list in H2; rewrite map_app in H2.
    unfold shift_list.
    repeat rewrite map_app.
    rewrite <- map_length with (l:= g1) (f:= shift_type 1 0).
    rewrite <- map_length with (l:= g2) (f:= shift_type 1 0).
    apply IHe. apply H2.
Abort.

Lemma subst_exp_pre : forall e s Ts T ctx ctx',
    (ctx' ++ Ts :: ctx) |- e \in T ->
    ctx |- s \in Ts ->
    (ctx' ++ ctx) |- subst_exp (length ctx') s e \in T.
Proof.
  induction e; simpl; intros.
  -
    inversion H; subst.
    destruct eqb eqn:IH1.
    apply eqb_eq in IH1; subst.
    admit.
    destruct ltb eqn:IH2.
    destruct n; try discriminate; simpl.
    constructor.
    apply ltb_lt in IH2.
    admit.
    constructor.
    admit.
  -
    inversion H; subst.
    constructor; eauto.
    assert (S (length ctx') = (length (t0:: ctx'))). reflexivity.
    rewrite H1.
    apply IHe with (Ts:= Ts) (ctx':= t0::ctx'); auto.
  -
    inversion H; subst.
    econstructor; eauto.
  -
    inversion H; subst.
    constructor.
    unfold shift_list in H3.
    repeat rewrite map_app in H3.
    unfold shift_list. repeat rewrite map_app.
    simpl in H3.
    admit.
  -
    inversion H; subst.
    econstructor; eauto.
Admitted.

Theorem T23_5_1 : forall e Γ ty e',
    Γ |- e \in ty -> e --> e' ->
    Γ |- e' \in ty.
Proof.
  intros. generalize dependent e'.
  induction H; intros; try solve_by_invert.
  - (*case: e = app*)
    inversion H1; subst; try econstructor; eauto.
    inversion H; subst.
    rewrite <- (app_nil_l Γ).
    apply subst_exp_pre with ty1; auto.
  -
    inversion H0; subst; try econstructor; eauto.
    inversion H; subst.
    clear IHhas_type.
    admit.
Abort.
