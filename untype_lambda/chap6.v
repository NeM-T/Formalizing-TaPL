Inductive term : Type :=
| Var : nat -> term
| Abs : term -> term
| App : term -> term -> term.

Fixpoint shift (d c: nat) (t: term) : term :=
  match t with
  | Var k =>
    if Nat.leb c k then Var (k + d) else Var k
  | Abs t1 => Abs (shift d (c + 1) t1)
  | App t1 t2 => App (shift d c t1) (shift d c t2)
  end.


Compute ( shift 2 0 (Abs (Abs (App (Var 1) (App (Var 0) (Var 2) ))))).
Compute ( shift 2 0 (Abs (App (Var 0) (App (Var 1)(Abs (App (Var 0)(App (Var 1)(Var 2)))))))).

Fixpoint subst (j: nat) (s t: term) : term :=
  match t with
  | Var k =>
    if Nat.eqb j k then s else Var k
  | Abs t1 =>
    Abs (subst (j + 1) (shift 1 0 s) t1)
  | App t1 t2 =>
    App (subst j s t1) (subst j s t2)
  end.

Compute (subst 0 (Var 1) (App (Var 0) (Abs(Abs (Var 2))))).
Compute (subst 0 (App (Var 1) (Abs (Var 2))) (App (Var 0) (Abs (Var 1)))).