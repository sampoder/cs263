/- Inductosolve coverage tests for Homework problems.
   Each theorem that compiles = solved. Definitions are copied from
   `Homework/Homework{2,3,4}.lean` since `Homework/` isn't a lake library. -/

import LoVe.LoVelib
import LoVe.LoVe06_InductivePredicates_Demo

namespace LoVe
namespace HomeworkTest

-- ============================================================
-- Homework 2 Q6: sum / snoc / reverse
-- ============================================================

def snoc {α : Type} : List α → α → List α
  | [],      n => [n]
  | m :: ms, n => m :: snoc ms n

def reverse {α : Type} : List α → List α
  | []      => []
  | m :: ms => snoc (reverse ms) m

def sum : List ℕ → ℕ
  | []      => 0
  | m :: ms => m + sum ms

theorem T_sum_snoc (ms : List ℕ) (n : ℕ) :
    sum (snoc ms n) = n + sum ms := by
  inductosolve? [sum, snoc]

theorem T_sum_append (ms ns : List ℕ) :
    sum (ms ++ ns) = sum ms + sum ns := by
  inductosolve? [sum]

theorem T_sum_reverse (ns : List ℕ) :
    sum (reverse ns) = sum ns := by
  inductosolve? [sum, reverse, T_sum_snoc]

-- ============================================================
-- Homework 3 Q1: Even / Odd (rule induction — expected fail)
-- ============================================================

-- HW3 defines its own Odd; redefine here so test uses the same shape.
inductive Odd' : ℕ → Prop
  | one             : Odd' 1
  | add_two (k : ℕ) : Odd' k → Odd' (k + 2)

theorem T_Odd_Even {n : ℕ} (hodd : Odd' n) : Even (n + 1) := by
  inductosolve?

theorem T_Even_Not_Odd {n : ℕ} (heven : Even n) : ¬ Odd n := by
  inductosolve?

theorem T_Even_add (m n : ℕ) (e_m : Even m) (e_n : Even n) :
    Even (m + n) := by
  inductosolve?

theorem T_Even_mul_two : ∀ (m : ℕ), Even (m * 2) := by
  intro m; inductosolve? [Nat.succ_mul, Nat.mul_succ, Nat.mul_two]

theorem T_Even_mul_even (m n : ℕ) (h : Even m) : Even (m * n) := by
  inductosolve? [Nat.add_mul, Nat.mul_add, Nat.two_mul, T_Even_add, T_Even_mul_two]

-- ============================================================
-- Homework 3 Q2: Gauss
-- ============================================================

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

theorem T_sumUpToOfFun_eq (n : ℕ) :
    2 * sumUpToOfFun id n = n * (n + 1) := by
  inductosolve? [sumUpToOfFun]

theorem T_sumUpToOfFun_mul (f g : ℕ → ℕ) (n : ℕ) :
    sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n := by
  inductosolve? [sumUpToOfFun]

-- ============================================================
-- Homework 3 Q3: Subseq
-- ============================================================

inductive Subseq {α : Type} : List α → List α → Prop where
  | rfl xs : Subseq xs xs
  | drop (y : α) (xs ys : List α) : Subseq xs ys → Subseq xs (y :: ys)
  | keep (x : α) (xs ys : List α) : Subseq xs ys → Subseq (x :: xs) (x :: ys)

theorem T_Subseq_empty {α : Type} (xs : List α) : Subseq [] xs := by
  inductosolve [Subseq.rfl, Subseq.drop]

theorem T_Subseq_empty_iff_empty {α : Type} (xs : List α) :
    Subseq xs [] ↔ xs = [] := by
  apply Iff.intro
  . inductosolve [Subseq.rfl]
  . intro h; rw [h]; exact Subseq.rfl []

theorem T_Subseq_concat_same {α : Type} (xs a b : List α) :
    Subseq a b → Subseq (xs ++ a) (xs ++ b) := by
  inductosolve [Subseq.keep]

theorem T_Subseq_concat {α : Type} (a' a b' b : List α) :
    Subseq a' a → Subseq b' b → Subseq (a' ++ b') (a ++ b) := by
  intro h1 h2; inductosolve [T_Subseq_concat_same]

-- ============================================================
-- Homework 3 Q5: List monad laws
-- ============================================================

def bind' {α β : Type} : List α → (α → List β) → List β
  | [],      _ => []
  | a :: as, f => f a ++ bind' as f

def pure' {α : Type} (a : α) : List α := [a]

theorem T_bind_append {α β : Type} (f : α → List β) (as as' : List α) :
    bind' (as ++ as') f = bind' as f ++ bind' as' f := by
  inductosolve [bind']

theorem T_bind_pure {α : Type} (as : List α) : bind' as pure' = as := by
  inductosolve [bind', pure']

theorem T_bind_assoc {α β γ : Type} (f : α → List β) (g : β → List γ)
    (as : List α) :
    bind' (bind' as f) g = bind' as (fun a ↦ bind' (f a) g) := by
  inductosolve [bind', T_bind_append]

theorem T_bind_pure_comp_eq_map {α β : Type} {f : α → β} (as : List α) :
    bind' as (fun a ↦ pure' (f a)) = List.map f as := by
  inductosolve [bind', pure']

-- ============================================================
-- Homework 4 Q1: type soundness for a tiny calculator
-- ============================================================

inductive Exp : Type
  | nat (n : ℕ) : Exp
  | bool (b : Bool) : Exp
  | var (x : String) : Exp
  | ite (e₁ e₂ e₃ : Exp) : Exp
  | add (e₁ e₂ : Exp) : Exp
  | le (e₁ e₂ : Exp) : Exp

inductive Val : Type
  | nat (n : ℕ) : Val
  | bool (b : Bool) : Val

abbrev Env : Type := String → Option Val

inductive Eval : Env → Exp → Val → Prop
  | nat (ρ : Env) (n : ℕ) : Eval ρ (Exp.nat n) (Val.nat n)
  | bool (ρ : Env) (b : Bool) : Eval ρ (Exp.bool b) (Val.bool b)
  | var (ρ : Env) (x : String) (v : Val) :
      ρ x = some v → Eval ρ (Exp.var x) v
  | ite_true (ρ : Env) (e₁ e₂ e₃ : Exp) (v : Val) :
      Eval ρ e₁ (Val.bool true) → Eval ρ e₂ v →
      Eval ρ (Exp.ite e₁ e₂ e₃) v
  | ite_false (ρ : Env) (e₁ e₂ e₃ : Exp) (v : Val) :
      Eval ρ e₁ (Val.bool false) → Eval ρ e₃ v →
      Eval ρ (Exp.ite e₁ e₂ e₃) v
  | add (ρ : Env) (e₁ e₂ : Exp) (n₁ n₂ : ℕ) :
      Eval ρ e₁ (Val.nat n₁) → Eval ρ e₂ (Val.nat n₂) →
      Eval ρ (Exp.add e₁ e₂) (Val.nat (n₁ + n₂))
  | le (ρ : Env) (e₁ e₂ : Exp) (n₁ n₂ : ℕ) :
      Eval ρ e₁ (Val.nat n₁) → Eval ρ e₂ (Val.nat n₂) →
      Eval ρ (Exp.le e₁ e₂) (Val.bool (n₁ ≤ n₂))

inductive Ty : Type
  | nat : Ty
  | bool : Ty

abbrev Ctx : Type := String → Option Ty

inductive ValHasType : Val → Ty → Prop
  | nat (n : ℕ) : ValHasType (Val.nat n) Ty.nat
  | bool (b : Bool) : ValHasType (Val.bool b) Ty.bool

inductive HasType : Ctx → Exp → Ty → Prop
  | nat (Γ : Ctx) (n : ℕ) : HasType Γ (Exp.nat n) Ty.nat
  | bool (Γ : Ctx) (b : Bool) : HasType Γ (Exp.bool b) Ty.bool
  | var (Γ : Ctx) (x : String) (τ : Ty) :
      Γ x = some τ → HasType Γ (Exp.var x) τ
  | ite (Γ : Ctx) (e₁ e₂ e₃ : Exp) (τ : Ty) :
      HasType Γ e₁ Ty.bool → HasType Γ e₂ τ → HasType Γ e₃ τ →
      HasType Γ (Exp.ite e₁ e₂ e₃) τ
  | add (Γ : Ctx) (e₁ e₂ : Exp) :
      HasType Γ e₁ Ty.nat → HasType Γ e₂ Ty.nat →
      HasType Γ (Exp.add e₁ e₂) Ty.nat
  | le (Γ : Ctx) (e₁ e₂ : Exp) :
      HasType Γ e₁ Ty.nat → HasType Γ e₂ Ty.nat →
      HasType Γ (Exp.le e₁ e₂) Ty.bool

def EnvModels (Γ : Ctx) (ρ : Env) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, ρ x = some v ∧ ValHasType v τ

theorem T_Eval_type_sound {Γ : Ctx} {ρ : Env} {e : Exp} {τ : Ty} :
    HasType Γ e τ →
    EnvModels Γ ρ →
    ∃ v, Eval ρ e v ∧ ValHasType v τ := by
  inductosolve

end HomeworkTest
end LoVe
