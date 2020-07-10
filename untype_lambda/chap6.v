Inductive term : Type :=
| Var : nat -> term
| Abs : term -> term
| App : term -> term -> term.

Notation beta_ShiftNum := 0.

Fixpoint shift (d c: nat) (t: term) : term :=
  match t with
  | Var k =>
    if Nat.leb c k then
      match d with
      | beta_ShiftNum => Var (k - 1)
      | _ => Var (k + d)
      end
    else Var k
  | Abs t1 => Abs (shift d (c + 1) t1)
  | App t1 t2 => App (shift d c t1) (shift d c t2)
  end.

Definition up (n: nat) (t: term) : term := shift n 0 t.

Compute ( up 2 (Abs (Abs (App (Var 1) (App (Var 0) (Var 2) ))))). (* = Abs (Abs (App (Var 1) (App (Var 0) (Var 4)))) *)
Compute ( up 2 (Abs (App (Var 0) (App (Var 1)(Abs (App (Var 0)(App (Var 1)(Var 2)))))))). (* = Abs (App (Var 0) (App (Var 3) (Abs (App (Var 0) (App (Var 1) (Var 4)))))) *)

Fixpoint subst (j: nat) (s t: term) : term :=
  match t with
  | Var k =>
    if Nat.eqb j k then s else Var k
  | Abs t1 =>
    Abs (subst (j + 1) (up 1 s) t1)
  | App t1 t2 =>
    App (subst j s t1) (subst j s t2)
  end.

Compute (subst 0 (Var 1) (App (Var 0) (Abs(Abs (Var 2))))).  (* = App (Var 1) (Abs (Abs (Var 3))) *)
Compute (subst 0 (App (Var 1) (Abs (Var 2))) (App (Var 0) (Abs (Var 1)))). (* = App (App (Var 1) (Abs (Var 2))) (Abs (App (Var 2) (Abs (Var 3)))) *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive value : term -> Prop :=
  | v_abs : forall n,
      value (Abs n).

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive eval : term -> term -> Prop :=
  | E_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         App t1 t2 --> App t1' t2
  | E_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         App v1 t2 --> App v1 t2'
  | E_AppAbs : forall t1 v2,
         value v2 ->
         App (Abs t1) v2 -->
             up beta_ShiftNum ([0 := up 1 (v2)] t1)

  where " t '-->' t' " := (eval t t').
