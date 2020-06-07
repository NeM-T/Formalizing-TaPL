Require Coq.extraction.Extraction.
Extraction Language OCaml.

Inductive term : Type :=
| tru
| fls
| If (t1 t2 t3: term)
| O
| succ (t1: term)
| pred (t1: term)
| iszero (t1: term).


Fixpoint isnumericval (t: term): bool :=
  match t with
  | O => true
  | succ t1 => isnumericval t1
  | _ => false
  end.

Fixpoint isval (t: term) : bool :=
  match t with
  | tru => true
  | fls => true
  | _ => isnumericval t
  end.

Inductive optiont : Type :=
| Some (t: term)
| None.

Fixpoint eval1 (t: term) : optiont :=
  match t with
  | If t1 t2 t3 =>
    if (isval t1) then
      match t1 with
      | tru => Some t2
      | fls => Some t3
      | _ => None
      end else
      match (eval1 t1) with
      | Some t1' => Some (If t1' t2 t3)
      | _ => None
      end
  | succ t1 =>
    if isnumericval t1 then
      None else
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
      end else
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
      end else
      match (eval1 t1) with
      | Some t1' => Some (iszero t1')
      | _ => None
      end
  | _ => None
  end.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Theorem eval1value : forall t1,
    isval t1 = true -> eval1 t1 = None.
Proof.
  intros. induction t1; try solve_by_inverts 2; try reflexivity.
  inversion H. simpl. rewrite H1; auto.
Qed.


Extraction "ocaml/eval.ml" eval1.

Inductive NatValue: term -> Prop :=
| nv_O : NatValue O
| nv_S : forall nv1, NatValue nv1 -> NatValue (succ nv1).

Inductive Pvalue: term -> Prop :=
| v_tru : Pvalue tru
| v_fls : Pvalue fls
| v_nat : forall t1, NatValue t1 -> Pvalue t1.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step: term -> term -> Prop :=
| E_IfTrue : forall t2 t3,
    If tru t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If fls t2 t3 --> t3
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
    iszero O --> tru
| E_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) --> fls
| E_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

  where " t '-->' t' " := (step t t').


Lemma nat_value : forall t,
    NatValue t <-> isnumericval t = true.
Proof.
  split; intros.
  -
    induction H; auto.
  -
    induction t; try solve_by_invert.
    apply nv_O. inversion H. apply IHt in H1. apply nv_S; auto.
Qed.

Lemma isval_Pvalue : forall t,
    isval t = true <-> Pvalue t.
Proof.
  split; intros.
  -
    induction t; try solve_by_invert.
    apply v_tru. apply v_fls.
    apply v_nat; apply nv_O.
    inversion H. apply nat_value in H1. apply v_nat. apply nv_S; auto.
  -
    induction H; auto.
    unfold isval. inversion H; auto.
    simpl. apply nat_value; auto.
Qed.

Theorem step_eval1_correct : forall t1 t1',
    eval1 t1 = Some t1' <-> t1 --> t1'.
Proof.
  split.
  -
    intros. generalize dependent t1'.
    induction t1; intros; try solve_by_invert.
    +
      inversion H. 
      induction (isval t1_1).
      destruct t1_1; try solve_by_invert.
      inversion H1. apply E_IfTrue.
      inversion H1. apply E_IfFalse.
      induction (eval1 t1_1) eqn:IHt1; try solve_by_invert.
      inversion H1. inversion H1. apply E_If. apply IHt1_1; auto.
    +
      inversion H.
      destruct (isnumericval t1) eqn:IHnum. inversion H1.
      destruct (eval1 t1) eqn:IH. inversion H1. apply E_Succ. apply IHt1; auto.
      inversion H1.
    +
      inversion H. destruct (isnumericval t1) eqn:IHnum; try solve_by_invert.
      destruct t1; try solve_by_invert. inversion H1. apply E_PredZero.
      inversion H1. apply E_PredSucc. inversion IHnum. apply nat_value; subst; auto.
      destruct (eval1 t1); try solve_by_invert.
      inversion H1. apply E_Pred. apply IHt1; auto.
    +
      inversion H.
      destruct (isnumericval t1) eqn:IHnum.
      destruct t1; try solve_by_invert.
      inversion H1. apply E_IsZeroZero.
      inversion H1. apply E_IsZeroSucc. inversion IHnum. apply nat_value; auto.
      destruct (eval1 t1); try solve_by_invert.
      inversion H1. apply E_IsZero. apply IHt1; auto.
  -
    intros. induction H; try reflexivity.
    +
      simpl. destruct (isval t1) eqn:IHv.
      destruct t1; try solve_by_invert. inversion H. inversion IHstep.
      inversion IHv. rewrite H5 in H4. inversion H4.
      rewrite IHstep; auto.
    +
      simpl. destruct (isnumericval t1) eqn:IHnum.
      pose proof (eval1value t1).
      rewrite H0 in IHstep.
      inversion IHstep.
      unfold isval. destruct t1; try solve_by_invert; auto.

      destruct (eval1 t1); try solve_by_invert.
      inversion IHstep; auto.
    +
      simpl. apply nat_value in H. rewrite H; auto.
    +
      simpl. destruct (isnumericval t1) eqn:IHnum.
      destruct t1; try solve_by_invert.
      pose proof (eval1value (succ t1)).
      rewrite H0 in IHstep. inversion IHstep.
      simpl. inversion IHnum; auto.
      destruct (eval1 t1); try solve_by_invert.
      inversion IHstep; auto.
    +
      simpl.
      destruct (isnumericval nv1) eqn:IHnum; try solve_by_invert; auto.
      apply nat_value in H. rewrite H in IHnum; inversion IHnum.
    +
      simpl.
      destruct (isnumericval t1) eqn:IHnum.
      pose proof (eval1value t1). rewrite H0 in IHstep. inversion IHstep.
      unfold isval. destruct t1; try solve_by_invert; auto.
      destruct (eval1 t1); try solve_by_invert. inversion IHstep; auto.
Qed.



Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(*停止する保証がないのでbigstepは無理そう*)
(*
Fixpoint bstep (t: term) : optiont :=
  match t with
  | tru => Some tru
  | fls => Some fls
  | O => Some t
  | If t1 t2 t3 =>
    match (eval1 t1) with
    | Some t1' =>
      if (isval t1') then
        match t1' with
        | tru => bstep t2
        | fls => bstep t3
        | _ => None
        end else bstep (If t1' t2 t3)
    | None => None
    end
  | succ t1 =>
    match (eval1 t1) with
    | Some t1' =>
      if (isval t1') then
        match t1' with
        | O => Some (succ O)
        | succ _ => Some (t1')
        | _ => None
        end else bstep (succ t1')
    | None => None
    end
  | pred t1 =>
    match (eval1 t1) with
    | Some t1' =>
      if (isval t1') then
        match t1' with
        | O => Some O
        | succ nv1 => Some nv1
        | _ => None
        end else bstep (pred t1')
    | _ => None
    end
  | iszero t1 =>
    match (eval1 t1) with
    | Some t1' =>
      if (isval t1') then
        match t1' with
        | O => Some tru
        | succ _ => Some fls
        | _ => None
        end else bstep (iszero t1')
    | _ => None
    end
  end.
*)
