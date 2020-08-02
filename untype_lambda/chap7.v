Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Export ExtrOcamlChar.
Extract Inductive string => "char list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" ["true" "false"].
From Coq Require Import Lists.List.
Extraction Language OCaml.
Import ListNotations.

Definition context : Type :=
  list (string).

Inductive term : Type :=
| Var (n1 n2: nat)
| Abs (name: string) (t: term)
| App (t1 t2: term).

Definition ctxlen (ctx: context) :=
  length ctx.

Definition eqb_string s1 s2:=
  String.eqb s1 s2.

Fixpoint In (name: string) (l: context): bool :=
  match l with
    | [] => false
    | n1 :: m => if eqb_string name n1 then true else In name m
  end.

Fixpoint newname (ctx: context) (name: string) (n: nat) :=
  if  In name ctx then
    match n with
    | O => append name "10"
    | S n' => newname ctx (append name "'") (n')
    end
  else name.

Definition pickfreshname ctx name :=
  let name' := (newname ctx name 10) in
  (name' :: ctx, name').

Fixpoint eqb_nat (n1 n2: nat) :=
  match n1 with
  | 0 =>
    match n2 with
    | 0 => true
    | _ => false
    end
  | S n1' =>
    match n2 with
    | 0 => false
    | S n2' => eqb_nat n1' n2'
    end
  end.

Fixpoint leb (n1 n2: nat) :=
  if eqb_nat n1 n2 then true else
    match n2 with
    | 0 => false
    | S n2' => leb n1 n2'
    end.

Fixpoint index2name (n : nat) (ctx: context) :=
  match n with
  | 0 =>
    match ctx with
    | [] => None
    | x :: ctx' => Some x
    end
  | S n' =>
    match ctx with
    | [] => None
    | x :: ctx' => index2name n' ctx'
    end
  end.

Inductive N : Type :=
| P (n: nat)
| M1.

Fixpoint shift_walk c d t :=
    match t with
    | Var x n =>
      if leb c x then
        match d with
        | M1 =>
          Var (x - 1) (n - 1)
        | P d' =>
          Var (x + d') (n + d')
        end
      else
        match d with
        | M1 =>
          Var x (n - 1)
        | P d' =>
          Var x (n + d')
        end
    | Abs x t1 =>
      Abs x (shift_walk (S c) d t1)
    | App t1 t2 =>
      App (shift_walk c d t1) (shift_walk c d t2)
    end.

Definition shift d t := shift_walk 0 d t.

Fixpoint sub_walk j s c t :=
  match t with
  | Var x n =>
    let jc :=
        match c with
        | M1 => (j - 1)
        | P c' => (j + c')
        end
    in
    if eqb_nat x (jc) then
      shift c s (*k/k\*)
    else
      Var x n
  | Abs x t1 =>
    let sc :=
        match c with
        | M1 => P 0
        | P c' => P (c' + 1)
        end
    in
    Abs x (sub_walk j s sc t1)
  | App t1 t2 =>
    App (sub_walk j s c t1) (sub_walk j s c t2)
  end.

Definition sub j s t :=
  sub_walk j s (P 0) t.

Definition subtop s t :=
  shift (M1) (sub 0 (shift (P 1) s) t).

Definition isval t :=
  match t with
  | Abs _ _ => true
  | _ => false
  end.

Fixpoint eval t :=
  match t with
  | App t1 t2 =>
    match t1 with
    | Abs x t12 =>
      if isval t2 then
        Some (subtop t2 t12)
      else
        match eval t2 with
        | Some t2' =>
          Some (App t1 t2')
        | None => None
        end
    | _ =>
      match eval t1 with
      | Some t1' =>
        Some (App t1' t2)
      | None => None
      end
    end
  | _ => None
  end.

Notation " s1 ':+' s2 " := (append s1 s2) (at level 40).

Fixpoint printtm (ctx: context) (t: term) : string :=
  match t with
  | Abs x t1 =>
    let (ctx', x') := pickfreshname ctx x in
    "(λ" :+ x' :+ ". " :+ printtm ctx' t1 :+ ")"
  | App t1 t2 =>
    "(" :+ printtm ctx t1 :+ " " :+ printtm ctx t2 :+ ")"
  | Var x n =>
    if eqb_nat (ctxlen ctx) n then
      match index2name x ctx with
      | Some str => str
      | None => "None"
      end
    else
      "[BadIndex]"
  end.

Definition test_eval t :=
  match eval t with
  | Some t' => printtm [] t'
  | None => "NotEval"%string
  end.

(* (λ x. x)  λ y. y => λ y. y *)
Compute (test_eval (App (Abs "x" (Var 0 1)) (Abs "y" (Var 0 1)))).
Compute (eval (App (Abs "x" (Var 0 1)) (Abs "y" (Var 0 1)))).
(* TmAbs("y", TmVar(0, 1)) *)

(* (λ x. λ y. x) λ z. z => λ y. λ z. z *)
Compute (test_eval (App (Abs "x" (Abs "y" (Var 1 2))) (Abs "z" (Var 0 1)))).
Compute (eval (App (Abs "x" (Abs "y" (Var 1 2))) (Abs "z" (Var 0 1)))).
 (* TmAbs("y", TmAbs("z", TmVar(0, 2))) *)

(* (λ x. λ x'. x) (λ x. x) => λ x'. λ x. x *)
Compute (test_eval (App (Abs "x" (Abs "x'" (Var 1 2))) (Abs "x" (Var 0 1)))).
Compute (eval (App (Abs "x" (Abs "x" (Var 1 2))) (Abs "x" (Var 0 1)))).
 (* TmAbs("x", TmAbs("x", TmVar(0, 2))) *)

(* (λ x. λ y. x) (λ z. z) (λ w. w) => (λ y. λ z. z) (λ w. w) *)
Compute (test_eval (App (App (Abs "x" (Abs "y" (Var 1 2))) (Abs "z" (Var 0 1))) (Abs "w" (Var 0 1)))).
Compute (eval (App (App (Abs "x" (Abs "y" (Var 1 2))) (Abs "z" (Var 0 1))) (Abs "w" (Var 0 1)))).
(* TmApp(TmAbs("y", TmAbs("z", TmVar(0, 2))), TmAbs("w", TmVar(0, 1))) *)

(* (λ x. x) ((λ y. y) (λ z. z))  => (λ x. x) (λ z. z) *)
Compute (test_eval (App (Abs "x" (Var 0 1)) (App (Abs "y" (Var 0 1)) (Abs "z" (Var 0 1))))).
Compute (eval (App (Abs "x" (Var 0 1)) (App (Abs "y" (Var 0 1)) (Abs "z" (Var 0 1))))).
(* TmApp(TmAbs("x", TmVar(0, 1)), TmAbs("z", TmVar(0, 1))) *)

(* (λ x. x x) (λ x. x x) => (λ x. x x) (λ x. x x) *)
Compute (test_eval (App (Abs "x" (App (Var 0 1) (Var 0 1))) (Abs "x" (App (Var 0 1) (Var 0 1))))).
Compute (eval (App (Abs "x" (App (Var 0 1) (Var 0 1))) (Abs "x" (App (Var 0 1) (Var 0 1))))).
 (* TmApp(TmAbs("x", TmApp(TmVar(0, 1), TmVar(0, 1))), TmAbs("x", TmApp(TmVar(0, 1), TmVar(0, 1))) *)

Extraction "./ocaml/chap7/src/eval" eval printtm test_eval.
