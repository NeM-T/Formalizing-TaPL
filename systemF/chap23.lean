open nat bool

def leb : ℕ → ℕ → bool
| 0 _ := true
| (succ n) 0 := false
| (succ n) (succ m) := (leb n m)

lemma ltb_lt : ∀ n m,
  leb n m = true ↔ n <= m := sorry

inductive ty : Type
| tyvar : ℕ → ty
| arrow : ty → ty → ty
| tyall : ty → ty

open ty

def shift_type : ℕ → ℕ → ty → ty
| d c (tyvar n) := if (leb c n) then (tyvar (n + d)) else (tyvar n)
| d c (arrow t1 t2) := (arrow (shift_type d c t1) (shift_type d c t2))
| d c (tyall ty1) := (tyall (shift_type d (succ c) ty1))

inductive exp : Type
| var : ℕ → exp
| abs : exp → exp
| app : exp → exp → exp
| Λ : exp → exp
| tapp : exp → ty → exp

open exp

inductive bind : Type
| tybind : ty → bind
| tyvarbind : ℕ → bind

open bind

def context := (list bind)

inductive onestep_eval : exp → exp → Prop
| E_App1: ∀ e1 e2 e1',
          onestep_eval e1 e1' → onestep_eval (app e1 e2) (app e1' e2)
| E_App2 :∀ e1 e2 e2',
          onestep_eval e2 e2' → onestep_eval (app e1 e2) (app e1 e2')
