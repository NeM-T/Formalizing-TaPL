Load "../std".
Import Nat.

Definition tyid := nat.

Inductive type : Set :=
| tyvar : tyid -> type
| arrow : type -> type -> type
| all : type -> type.

Inductive exp : Set :=
| var : nat -> exp
| abs : type -> exp -> exp
| app : exp -> exp -> exp
| tabs : exp -> exp
| tapp : exp -> type -> exp.

Definition isval e :=
  match e with
  | abs _ _ => true
  | tabs _ => true
  | _ => false
  end.

Inductive bind : Set :=
| tybind : type -> bind
| tyvarbind : bind.

Definition context := (list bind).

Fixpoint shift_type d c ty :=
  match ty with
  | tyvar n => tyvar (if c <=? n then (n + d) else n)
  | arrow ty1 ty2 => arrow (shift_type d c ty1) (shift_type d c ty2)
  | all ty1 => all (shift_type d (S c) ty1)
  end.

Fixpoint subst_type (d: nat) (ty1 ty2: type) :=
  match ty1 with
  | tyvar n =>
    if d =? n then shift_type 0 d ty2
    else if d <? n then tyvar (pred n) else (tyvar n)
  | arrow t1 t2 => arrow (subst_type d t1 ty2) (subst_type d t2 ty2)
  | all t1 => all (subst_type (S d) t1 ty2)
  end.

Fixpoint shift_exp (d c : nat) (t : exp) :=
match t with
| var x => var (if c <=? x then x + d else x)
| abs ty e1 => abs (shift_type d c ty) (shift_exp d (S c) e1)
| app e1 e2 => app (shift_exp d c e1) (shift_exp d c e2)
| tabs e1 => tabs (shift_exp d (S c) e1)
| tapp e1 ty1 => tapp (shift_exp d c e1) (shift_type d c ty1)
end.

Fixpoint subst_exp (d : nat) (s t: exp) : exp :=
match t with
| var x => if d =? x then shift_exp 0 d s
           else if d <? x then var (pred x)
                else var x
| abs ty e1 => abs ty (subst_exp (S d) s e1)
| app e1 e2 => app (subst_exp d s e1) (subst_exp d s e2)
| tabs e1 => tabs (subst_exp (S d) s e1)
| tapp e1 ty => tapp (subst_exp d s e1) ty
end.

Notation " [[ X \ t2 ]] t1 " := (subst_exp X t2 t1) (at level 50).

Fixpoint subst_ty_exp (d: nat) (ty: type) (e: exp) : exp :=
  match e with
  | var _ => e
  | abs ty1 e1 => abs (subst_type d ty1 ty) (subst_ty_exp (S d) ty e1)
  | app e1 e2 => app (subst_ty_exp d ty e1) (subst_ty_exp d ty e2)
  | tabs e1 => tabs (subst_ty_exp d ty e1)
  | tapp e1 ty2 => tapp (subst_ty_exp d ty e1) (subst_type d ty2 ty)
  end.

Notation " [[ X |-->  T2 ]] t1 " := (subst_ty_exp X T2 t1) (at level 50).

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
  | tapp (tabs e1) ty => Some ( [[ 0 |--> ty ]] e1 )
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
  | all t1, all t2 => eqb_type t1 t2
  | _, _ => false
  end.

Fixpoint type_of (Γ: context) (e: exp) : option type :=
  match e with
  | var n =>
    match nth_opt Γ n with
    | Some (tybind ty) => Some ty
    | _ => None
    end
  | abs ty e1 =>
    match type_of (tybind (ty) :: Γ) e1 with
    | Some ty2 => Some (arrow ty ty2)
    | None => None
    end
  | app e1 e2 =>
    match type_of Γ e1, type_of Γ e2 with
    | Some (arrow ty1 ty), Some ty2 =>
      if eqb_type ty1 ty2 then (Some ty) else None
    | _, _ => None
    end
  | tabs e1 =>
    match type_of (tyvarbind :: Γ) e1 with
    | Some ty => Some (all ty)
    | None => None
    end
  | tapp e1 T2 =>
    match type_of Γ e1 with
    | Some (all ty1) => Some ( subst_type 0 ty1 T2)
    | _ => None
    end
  end.

Inductive value : exp -> Prop :=
| AbsV : forall ty e, value (abs ty e)
| TAbsV : forall e, value (tabs e).

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
    (tapp (tabs e) ty) --> [[ 0 |--> ty]]e
where "e1 --> e2" := (onestep e1 e2).

Reserved Notation "Γ |- e \in ty" (at level 40).
Inductive has_type : context -> exp -> type -> Prop :=
| T_Var : forall n Γ ty,
    nth_opt Γ n = Some (tybind ty) ->
    Γ |- (var n) \in ty
| T_Abs : forall Γ ty e T,
    (tybind T :: Γ) |- e \in ty ->
    Γ |- (abs T e) \in (arrow T ty)
| T_App : forall e1 e2 Γ ty1 ty2,
    Γ |- e1 \in arrow ty1 ty2 ->
    Γ |- e2 \in ty1 ->
    Γ |- (app e1 e2) \in ty2
| T_TAbs : forall e ty Γ,
    (tyvarbind :: Γ) |- e \in ty ->
    Γ |- tabs e \in all ty
| T_TApp : forall Γ e1 ty1 ty2,
    Γ |- e1 \in all ty1 ->
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
      destruct b; try discriminate. inversion H; subst; reflexivity.
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
    rewrite IHe, shift_ty0; reflexivity.
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
  destruct ctx. inversion H. simpl. destruct ( (b :: ctx) ++ ctx1) eqn:IHH. inversion H0. inversion IHH; subst.
  eapply IHn in H0. apply H0. simpl in H. apply lt_S_n in H. apply H.
Qed.

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
    apply IHe with (g1:= (tybind t0 :: g1)) (g2:= g2) in H4.
    simpl in H4.
    apply T_Abs in H4.
    admit.
  -
    econstructor; eauto.
    apply IHe with (g1:= tyvarbind :: g1). apply H2.
  -
    apply IHe with (g2:= g2) in H4.
Abort.

Theorem T23_5_1 : forall e Γ ty e',
    Γ |- e \in ty -> e --> e' ->
    Γ |- e' \in ty.
Proof.
  intros. generalize dependent e'.
  induction H; intros; try solve_by_invert.
  - (*case: e = app*)
    inversion H1; subst; try econstructor; eauto.
    admit.
  -
    inversion H0; subst; try econstructor; eauto.
    inversion H; subst.
    admit.
Abort.
