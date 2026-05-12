import AutograderLib
import LoVe.LoVelib

/- # Homework 4: 29 Points

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

section Q1_Types

/- ## Question 1 (Simple Typed Calculator)

We now work with a tiny calculator language featuring naturals, booleans,
variables, addition, comparison, and conditionals.

We will set up a big-step semantics for this language
to give it a semantics that evaluates expressions into values.

Then we will define a type system for this language and prove that well-typed
programs evaluate to values of the correct type (type safety). This is a very strong
theorem, as it also implies termination of well-typed programs (i.e. you get back a value at all!).
In other type systems, we might separate these.

-/

inductive Exp : Type
  | nat (n : ℕ) : Exp
  | bool (b : Bool) : Exp
  | var (x : String) : Exp
  | ite (e₁ e₂ e₃ : Exp) : Exp
  | add (e₁ e₂ : Exp) : Exp
  | le (e₁ e₂ : Exp) : Exp

-- an example `if cond then 7 else 9`
abbrev exp7or9 : Exp :=
  Exp.ite (Exp.var "cond") (Exp.nat 7) (Exp.nat 9)

inductive Val : Type
  | nat (n : ℕ) : Val
  | bool (b : Bool) : Val

abbrev Env : Type := String → Option Val

def emptyEnv : Env := fun _ => none

def Env.update (ρ: Env) (x : String) (v : Val) : Env :=
  fun y => if y = x then some v else ρ y

/-- Big-step evaluation relation. -/
inductive Eval : Env → Exp → Val → Prop
  | nat (ρ : Env) (n : ℕ) :
      Eval ρ (Exp.nat n) (Val.nat n)
  | bool (ρ : Env) (b : Bool) :
      Eval ρ (Exp.bool b) (Val.bool b)
  | var (ρ : Env) (x : String) (v : Val) :
      ρ x = some v →
      Eval ρ (Exp.var x) v
  | ite_true (ρ : Env) (e₁ e₂ e₃ : Exp) (v : Val) :
      Eval ρ e₁ (Val.bool true) →
      Eval ρ e₂ v →
      Eval ρ (Exp.ite e₁ e₂ e₃) v
  | ite_false (ρ : Env) (e₁ e₂ e₃ : Exp) (v : Val) :
      Eval ρ e₁ (Val.bool false) →
      Eval ρ e₃ v →
      Eval ρ (Exp.ite e₁ e₂ e₃) v
  | add (ρ : Env) (e₁ e₂ : Exp) (n₁ : ℕ) (n₂ : ℕ) :
      Eval ρ e₁ (Val.nat n₁) →
      Eval ρ e₂ (Val.nat n₂) →
      Eval ρ (Exp.add e₁ e₂) (Val.nat (n₁ + n₂))
  | le (ρ : Env) (e₁ e₂ : Exp) (n₁ : ℕ) (n₂ : ℕ) :
      Eval ρ e₁ (Val.nat n₁) →
      Eval ρ e₂ (Val.nat n₂) →
      Eval ρ (Exp.le e₁ e₂) (Val.bool (n₁ <= n₂))
  /- Fill in the two missing evaluation rules for `add` and `le`.
     `add` evaluates to the sum of the two arguments.
     `le x y` evaluates to the boolean `x ≤ y`.
  -/


/- Inversion lemmas for Eval -/

@[simp, autogradedProof 1]
theorem Eval_nat {ρ : Env} {n : ℕ} {v : Val} :
    Eval ρ (Exp.nat n) v ↔ v = Val.nat n := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; simp [Eval.nat]

@[simp, autogradedProof 1]
theorem Eval_bool {ρ : Env} {b : Bool} {v : Val} :
    Eval ρ (Exp.bool b) v ↔ v = Val.bool b := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; simp [Eval.bool]

@[simp, autogradedProof 1]
theorem Eval_var {ρ : Env} {x : String} {v : Val} :
    Eval ρ (Exp.var x) v ↔ ρ x = some v := by
  constructor
  · intro h; cases h; exact a
  · intro h; apply (Eval.var ρ x v h)

@[simp, autogradedProof 1]
theorem Eval_add {ρ : Env} {e₁ e₂ : Exp} {v : Val} :
    Eval ρ (Exp.add e₁ e₂) v ↔
    (∃n₁ n₂, Eval ρ e₁ (Val.nat n₁) ∧ Eval ρ e₂ (Val.nat n₂) ∧ v = Val.nat (n₁ + n₂)) := by
  constructor
  · intro h; cases h; exact ⟨n₁, n₂, by assumption, by assumption, rfl⟩
  · intro ⟨n₁, n₂, h₁, h₂, hv⟩; rw [hv]; exact Eval.add ρ e₁ e₂ n₁ n₂ h₁ h₂

@[simp, autogradedProof 1]
theorem Eval_le {ρ : Env} {e₁ e₂ : Exp} {v : Val} :
    Eval ρ (Exp.le e₁ e₂) v ↔
    (∃n₁ n₂, Eval ρ e₁ (Val.nat n₁) ∧ Eval ρ e₂ (Val.nat n₂) ∧ v = Val.bool (n₁ ≤ n₂)) := by
  constructor
  · intro h; cases h; exact ⟨n₁, n₂, by assumption, by assumption, rfl⟩
  · intro ⟨n₁, n₂, h₁, h₂, hv⟩; rw [hv]; exact Eval.le ρ e₁ e₂ n₁ n₂ h₁ h₂

@[simp, autogradedProof 1]
theorem Eval_ite {ρ : Env} {e₁ e₂ e₃ : Exp} {v : Val} :
    Eval ρ (Exp.ite e₁ e₂ e₃) v ↔
    (Eval ρ e₁ (Val.bool true) ∧ Eval ρ e₂ v) ∨
    (Eval ρ e₁ (Val.bool false) ∧ Eval ρ e₃ v) := by
  constructor
  · intro h
    cases h with
    | ite_true _ _ _ _ h₁ h₂ => exact Or.inl (And.intro h₁ h₂)
    | ite_false _ _ _ _ h₁ h₂ => exact  Or.inr (And.intro h₁ h₂)
  . intro h
    cases h with
    | inl a => apply (Eval.ite_true ρ); exact (And.left a); exact (And.right a)
    | inr a => apply (Eval.ite_false ρ); exact (And.left a); exact (And.right a)

-- with all those inversion lemmas in place, we can easily evaluate `exp7or9`
example: Eval (emptyEnv.update "cond" (Val.bool true))  exp7or9 (Val.nat 7) := by simp; rfl
example: Eval (emptyEnv.update "cond" (Val.bool false)) exp7or9 (Val.nat 9) := by simp; rfl

/-- Types, contexts, and a typing relation -/

inductive Ty : Type
  | nat : Ty
  | bool : Ty

abbrev Ctx : Type := String → Option Ty

def emptyCtx : Ctx := fun _ => none

def Ctx.update (Γ: Ctx) (x : String) (t : Ty) : Ctx :=
  fun y => if y = x then some t else Γ y

/-- A simple typing relation for values -/
inductive ValHasType : Val → Ty → Prop
  | nat (n : ℕ) : ValHasType (Val.nat n) Ty.nat
  | bool (b : Bool) : ValHasType (Val.bool b) Ty.bool

/-- Inversion rules for ValHasType -/

@[simp, autogradedProof 1]
theorem ValHasType_nat_inv (v : Val) :
    ValHasType v Ty.nat ↔ ∃ n, v = Val.nat n := by
  constructor
  . intro h; cases h; simp
  . intro h; cases h; rw [h_1]; exact ValHasType.nat w

@[simp, autogradedProof 1]
theorem ValHasType_bool_inv (v : Val) :
    ValHasType v Ty.bool ↔ ∃ b, v = Val.bool b := by
  constructor
  . intro h; cases h; simp
  . intro h; cases h; rw [h_1]; exact ValHasType.bool w

/-- Typing relation for expressions.

This inductive predicate defines when an expression `e` has type `τ` under a typing context `Γ`.
As before, we can read the constructors of an inductive predicate as proof rules, so
this __is__ the definition of the type system for our language. Each constructor corresponds to a typing rule.
 -/

inductive HasType : Ctx → Exp → Ty → Prop
  | nat (Γ : Ctx) (n : ℕ) :
      HasType Γ (Exp.nat n) Ty.nat
  | bool (Γ : Ctx) (b : Bool) :
      HasType Γ (Exp.bool b) Ty.bool
  | var (Γ : Ctx) (x : String) (τ : Ty) :
      Γ x = some τ →
      HasType Γ (Exp.var x) τ
  | ite (Γ : Ctx) (e₁ e₂ e₃ : Exp) (τ : Ty) :
      HasType Γ e₁ Ty.bool →
      HasType Γ e₂ τ →
      HasType Γ e₃ τ →
      HasType Γ (Exp.ite e₁ e₂ e₃) τ
  /- Fill in the two missing typing rules for `add` and `le`.
     `add` has type `nat` if both subexpressions have type `nat`.
     `le` has type `bool` if both subexpressions have type `nat`.
  -/
  | add (Γ : Ctx) (e₁ e₂: Exp) :
      HasType Γ e₁ Ty.nat →
      HasType Γ e₂ Ty.nat →
      HasType Γ (Exp.add e₁ e₂) Ty.nat
  | le (Γ : Ctx) (e₁ e₂: Exp) :
      HasType Γ e₁ Ty.nat →
      HasType Γ e₂ Ty.nat →
      HasType Γ (Exp.le e₁ e₂) Ty.bool



/- 5.1 (2 points). Prove inversion lemmas for typing. -/

@[simp, autogradedProof 1]
theorem HasType_nat_inv {Γ : Ctx} {n : ℕ} {τ : Ty} :
    HasType Γ (Exp.nat n) τ ↔ τ = Ty.nat := by
  constructor
  . intro h; cases h; simp
  . intro h; cases h; apply HasType.nat

@[simp, autogradedProof 1]
theorem HasType_bool_inv {Γ : Ctx} {b : Bool} {τ : Ty} :
    HasType Γ (Exp.bool b) τ ↔ τ = Ty.bool := by
  constructor
  . intro h; cases h; simp
  . intro h; cases h; apply HasType.bool

@[simp, autogradedProof 1]
theorem HasType_var_inv {Γ : Ctx} {x : String} {τ : Ty} :
    HasType Γ (Exp.var x) τ ↔ Γ x = some τ := by
  constructor
  . intro h; cases h; exact a
  . intro h; apply HasType.var; exact h

@[simp, autogradedProof 1]
theorem HasType_add_inv {Γ : Ctx} {e₁ e₂ : Exp} :
    HasType Γ (Exp.add e₁ e₂) Ty.nat ↔
    HasType Γ e₁ Ty.nat ∧ HasType Γ e₂ Ty.nat := by
  constructor
  . intro h; cases h; exact And.intro a a_1
  . intro h; cases h; exact (HasType.add Γ e₁ e₂ left right)

@[simp, autogradedProof 1]
theorem HasType_le_inv {Γ : Ctx} {e₁ e₂ : Exp} :
    HasType Γ (Exp.le e₁ e₂) Ty.bool ↔
    HasType Γ e₁ Ty.nat ∧ HasType Γ e₂ Ty.nat := by
  constructor
  . intro h; cases h; exact And.intro a a_1
  . intro h; cases h; exact (HasType.le Γ e₁ e₂ left right)

@[simp, autogradedProof 1]
theorem HasType_ite_inv {Γ : Ctx} {e₁ e₂ e₃ : Exp} {τ : Ty} :
    HasType Γ (Exp.ite e₁ e₂ e₃) τ ↔
    HasType Γ e₁ Ty.bool ∧ HasType Γ e₂ τ ∧ HasType Γ e₃ τ := by
  constructor
  . intro h; cases h; exact And.intro a (And.intro a_1 a_2)
  . intro h; cases h; exact (HasType.ite Γ e₁ e₂ e₃ τ left (And.left right) (And.right right))

-- with these inversion lemmas, we can easily check that `exp7or9` has type `nat`
-- when the variable `cond` has type `bool`
example: HasType (emptyCtx.update "cond" Ty.bool) exp7or9 Ty.nat := by simp; rfl


/- 5.3 (4 points). Prove semantic type soundness.

If `Γ ⊢ e : τ` (i.e. `HasType Γ e τ`), `ρ` models `Γ`, and `e` evaluates to `v` under `ρ`,
then `v` has type `τ`.
-/

/-- A predicate stating that a typing context `Γ` agrees with an environment `ρ`.
 `ρ` models `Γ` if each variable in `Γ` maps in `ρ` to a value of that type.

  You will need this for the `var` case of the type soundness proof.
  -/
def EnvModels (Γ : Ctx) (ρ : Env) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, ρ x = some v ∧ ValHasType v τ


@[autogradedProof 4]
theorem Eval_type_sound {Γ : Ctx} {ρ : Env} {e : Exp} {τ : Ty} :
    HasType Γ e τ →
    EnvModels Γ ρ →
    ∃v, Eval ρ e v ∧ ValHasType v τ
  := by
  intro hty hmod
  induction hty with
  | nat n => simp
  | bool b => simp
  | var x τ _ => simp; exact hmod x τ a;
  | ite e₁ e₂ e₃ τ _ _ _ _ _ _ =>
    obtain ⟨v, v_eval, v_type⟩ := a_ih;
    rw [ValHasType_bool_inv] at v_type;
    obtain ⟨b, hb⟩ := v_type
    rw [hb] at v_eval
    cases b
    . obtain ⟨v3, v3_eval, v3_type⟩ := a_ih_2;
      simp [v_eval]
      exact Exists.intro v3 (And.intro (Or.inr v3_eval) v3_type)
    . obtain ⟨v2, v2_eval, v2_type⟩ := a_ih_1;
      simp [v_eval];
      exact Exists.intro v2 (And.intro (Or.inl v2_eval) v2_type)

  | add e₁ e₂ _ _ _ _ =>
    obtain ⟨v, v_eval, v_type⟩ := a_ih;
    obtain ⟨v1, v1_eval, v1_type⟩ := a_ih_1;
    simp;
    rw [ValHasType_nat_inv] at v_type;
    rw [ValHasType_nat_inv] at v1_type;
    obtain ⟨b, hb⟩ := v_type
    rw [hb] at v_eval
    obtain ⟨b1, hb1⟩ := v1_type
    rw [hb1] at v1_eval
    exact And.intro (Exists.intro b v_eval) (Exists.intro b1 v1_eval)
  | le e₁ e₂ _ _ _ _ =>
    -- you may want to use `simp [Nat.lt_or_ge]` at some point in this case
    obtain ⟨v, v_eval, v_type⟩ := a_ih;
    obtain ⟨v1, v1_eval, v1_type⟩ := a_ih_1;
    simp [Nat.lt_or_ge]
    rw [ValHasType_nat_inv] at v_type;
    rw [ValHasType_nat_inv] at v1_type;
    obtain ⟨b, hb⟩ := v_type
    rw [hb] at v_eval
    obtain ⟨b1, hb1⟩ := v1_type
    rw [hb1] at v1_eval
    exact And.intro (Exists.intro b v_eval) (Exists.intro b1 v1_eval)

/-- Our type system (like many!) is sound but incomplete: there are some expressions
    that evaluate to values but are not typable. Here's a hint: construct an expression
    where the type system is too conservative, thinking that one of two things
    could happen, but in fact only one of them can happen in the big-step semantics.

    Find one that works in the empty context.
    The proof should be a simple `exists YOUR_EXPRESSION; simp`.
    -/
@[autogradedProof 1]
theorem HasType_Incomplete :
  ∃e v,
   Eval emptyEnv e v ∧
   ¬∃τ, HasType emptyCtx e τ :=
  by
  exists (Exp.ite (Exp.bool true) (Exp.bool false) (Exp.nat 3)), (Val.bool false)
  simp

end Q1_Types

section Q2_Finsets

/- ## Question 2 (10 points): Finsets from Lists via Quotients

In this question, we represent finite sets by quotienting lists by having the
same membership relation. Intuitively, list order and duplicate elements
should not matter.

We define two lists to be equivalent if they contain exactly the same elements.
-/

abbrev ListSetEquiv {α : Type} (xs ys : List α) : Prop :=
  ∀ a, a ∈ xs ↔ a ∈ ys

@[autogradedProof 1]
theorem ListSetEquiv_refl {α : Type} (xs : List α) :
    ListSetEquiv xs xs := by
  simp [ListSetEquiv]

@[autogradedProof 1]
theorem ListSetEquiv_symm {α : Type} {xs ys : List α} :
    ListSetEquiv xs ys → ListSetEquiv ys xs := by
  simp [ListSetEquiv]
  intro h b
  simp [h]

@[autogradedProof 1]
theorem ListSetEquiv_trans {α : Type} {xs ys zs : List α} :
    ListSetEquiv xs ys → ListSetEquiv ys zs → ListSetEquiv xs zs := by
  simp [ListSetEquiv]
  intro a b c
  simp [a, b]

instance ListSetoid (α : Type) : Setoid (List α) where
  r := ListSetEquiv
  iseqv := {
    refl := ListSetEquiv_refl
    symm := ListSetEquiv_symm
    trans := ListSetEquiv_trans
  }

abbrev FinSet (α : Type) : Type :=
  Quotient (ListSetoid α)

@[autogradedDef 1]
def finsetEmpty {α : Type} : FinSet α :=
  ⟦[]⟧

@[autogradedDef 1]
def finsetSingleton {α : Type} (a : α) : FinSet α :=
  ⟦[a]⟧

@[autogradedDef 1]
def finsetUnion {α : Type} (x y : FinSet α) : FinSet α :=
  Quotient.liftOn₂ x y
    (fun xs ys => ⟦xs ++ ys⟧)
    (by
      intro a b c d e f
      apply Quotient.sound
      intro x
      simp [e x, f x]
    )

instance FinSet.instZero {α : Type} : Zero (FinSet α) :=
  ⟨finsetEmpty⟩

instance FinSet.instAdd {α : Type} : Add (FinSet α) :=
  ⟨finsetUnion⟩

@[autogradedProof 1]
theorem finset_zero_add {α : Type} (x : FinSet α) :
    0 + x = x := by
  -- some skeleton code to get you started
  induction x using Quotient.inductionOn
  apply Quotient.sound
  -- this intro is useful to "see through" the definition of ≈ and get to
  -- to the underlying ListSetEquiv relation
  intro b
  simp

@[autogradedProof 1]
theorem finset_add_comm {α : Type} (x y : FinSet α) :
    x + y = y + x := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  apply Quotient.sound
  intro b
  simp [Or.comm]



@[autogradedProof 1]
theorem finset_add_assoc {α : Type} (x y z : FinSet α) :
    (x + y) + z = x + (y + z) := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  induction z using Quotient.inductionOn
  apply Quotient.sound
  intro b
  simp

-- this one should be easy given the previous couple of theorems
@[autogradedProof 1]
theorem finset_add_zero {α : Type} (x : FinSet α) :
    x + 0 = x := by
  induction x using Quotient.inductionOn
  apply Quotient.sound
  simp


instance FinSet.instAddCommMonoid {α : Type} : AddCommMonoid (FinSet α) :=
{
  add_assoc := finset_add_assoc
  zero_add := finset_zero_add
  add_zero := finset_add_zero
  add_comm := finset_add_comm
  nsmul := nsmulRec
}

end Q2_Finsets

end LoVe
