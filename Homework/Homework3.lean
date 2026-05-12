import LoVe.LoVelib
import AutograderLib
import LoVe.LoVe07_EffectfulProgramming_Demo

namespace LoVe

/- # Homework 3: Inductive Predicates and Monads

Replace the placeholders (e.g., `:= sorry`) with your solutions.
Submit *only* this file to the appropriate Gradescope assignment.
-/

section Q1_Even_Odd
/- ## Question 1 (6 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- ### 1.1 (0 points).

Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `Even`,
and should not rely on `Even`. -/

inductive Odd : ℕ → Prop
  | one             : Odd 1
  | add_two (k : ℕ) : Odd k → Odd (k + 2)


/- ### 1.2 (1 point).

Give *proof terms* for the following propositions, based on
your answer to question 2.1. -/

@[autogradedProof 0.5]
theorem Odd_3 :
  Odd 3 :=
  (Odd.add_two 1 Odd.one)

@[autogradedProof 0.5]
theorem Odd_5 :
  Odd 5 :=
  (Odd.add_two _ (Odd.add_two 1 Odd.one))

/- ### 1.3 (1 point).

Prove the following theorem by rule induction: -/

@[autogradedProof 1]
theorem Odd_Even {n : ℕ} (hodd : Odd n) :
  Even (n + 1) :=
  by
    induction hodd with
    | one => exact (Even.add_two _ Even.zero)
    | add_two k a ih => exact (Even.add_two _ ih)


/- ### 1.4 (1 point).

Prove the following theorem using rule induction.

Hint: Recall that `¬ a` is defined as `a → false`. -/

@[autogradedProof 1]
theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
  ¬ Odd n :=
  by
    induction heven with
    | zero =>
      intro h
      contradiction
    | add_two n e a_ih =>
      intro h
      cases h
      contradiction


/- ### 1.5 (3 point).

Prove the following theorems.

These should short proofs with only a single induction each.
Use the first two theorems in the last one.
 -/
@[autogradedProof 1]
theorem Even_add :
  ∀ (m n : ℕ), Even m → Even n → Even (m + n) :=
  by
    intro m n e_m e_n
    induction e_m with
    | zero =>
      simp
      exact e_n
    | add_two k e_k e_k_n =>
      have e_k_n_2 := (Even.add_two _ e_k_n)
      rw [Nat.add_right_comm] at e_k_n_2
      exact e_k_n_2

-- You might need `Nat.mul_comm` and `Nat.mul_add`
@[autogradedProof 1]
theorem Even_mul_two :
  ∀ (m : ℕ), Even (m * 2) :=
  by
    intro m
    induction m with
    | zero => exact Even.zero
    | succ n h =>
      rw [Nat.mul_comm, Nat.mul_add]
      rw [Nat.mul_comm]
      exact Even.add_two (n * 2) h


-- You might need `Nat.mul_comm` and `Nat.mul_add`
@[autogradedProof 1]
theorem Even_mul_even:
  ∀ (m n : ℕ), Even m → Even (m * n) :=
  by
    intro m n h
    induction h with
    | zero =>
      simp
      exact Even.zero
    | add_two k e_k e_k_n =>
      rw [Nat.mul_comm, Nat.mul_add]
      have n_2 := n * 2
      have e_n_2 := Even_mul_two n
      rw [Nat.mul_comm] at e_k_n
      exact Even_add (n * k) (n * 2) e_k_n e_n_2

end Q1_Even_Odd


section Q2_Gauss
/- ## Question 2 (4 points): Gauss's Summation Formula

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`: -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- (2 points). Prove the following theorem, discovered by Carl Friedrich
Gauss as a pupil.

Hints:

* The `mul_add` and `add_mul` theorems might be useful to reason about
  multiplication.

* The `linarith` tactic introduced in lecture 6 might be useful to reason about
  addition. -/

#check mul_add
#check add_mul

@[autogradedProof 2]
theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun id m = m * (m + 1) :=
  by
    intro n
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      simp [sumUpToOfFun]
      rw [Nat.mul_add, ih]
      linarith

/- (2 points). Prove the following property of `sumUpToOfFun`. -/

@[autogradedProof 2]
theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n :=
  by
    intro n
    induction n with
    | zero =>
      simp [sumUpToOfFun]
    | succ n ih =>
      simp [sumUpToOfFun]
      linarith


end Q2_Gauss


namespace Q3_Subseq

/-

## Question 3 (4 points): Subsequences

Here we define an inductive predicate `Subseq xs ys`
 that holds if and only if `xs` is a subsequence of `ys`.
A subsequence of a list is a list that can be obtained by deleting zero or more elements from the original list,
 without changing the order of the remaining elements.

Prove the following theorems about `Subseq`.
You may want to induct on the structure of the `Subseq` proof terms,
or on the structure of the lists.
The reference solutions have 0 or 1 induction in each proof.

-/

inductive Subseq {α : Type} : List α → List α → Prop where
  | rfl xs : Subseq xs xs
  | drop (y : α) (xs ys : List α): Subseq xs ys → Subseq xs (y :: ys)
  | keep (x : α) (xs ys : List α): Subseq xs ys → Subseq (x :: xs) (x :: ys)

@[autogradedProof 1]
theorem Subseq_empty {α : Type} (xs : List α) :
  Subseq [] xs :=
  by
    induction xs with
    | nil =>
      simp [Subseq.rfl]
    | cons h t t_ih =>
      exact Subseq.drop h [] t t_ih

@[autogradedProof 1]
theorem Subseq_empty_iff_empty {α : Type} (xs : List α) :
  Subseq xs [] ↔ xs = [] :=
  by
    apply Iff.intro
    . induction xs
      . simp
      . intro head
        contradiction
    . intro first
      rw [first]
      exact Subseq.rfl []

@[autogradedProof 1]
theorem Subseq_concat_same {α : Type} (xs a b : List α):
  Subseq a b → Subseq (xs ++ a) (xs ++ b) :=
  by
    intro assumption
    induction xs with
    | nil => exact assumption
    | cons head tail tail_ih =>
      exact Subseq.keep _ _ _ tail_ih

@[autogradedProof 2]
theorem Subseq_concat {α : Type} (a' a b' b : List α):
  Subseq a' a → Subseq b' b → Subseq (a' ++ b') (a ++ b) :=
  by
    intro a_a b_b
    induction a_a with
    | rfl xs => exact Subseq_concat_same _ _ _ b_b
    | drop y xs ys a a_ih =>
      exact Subseq.drop _ _ _ a_ih
    | keep x xs ys a a_ih =>
      exact Subseq.keep _ _ _ a_ih

end Q3_Subseq


namespace Q4_FMap
/- ## Question 4 (4 points): `map` for Monads

We will define a `map` function for monads and derive its so-called functorial
properties from the three laws.

All of the reference solutions for this question are very short, a couple of lines.

(1 points). Define `map` on `m`. This function should not be confused
with `mmap` from the lecture's demo.

Hint: The challenge is to find a way to create a value of type `m β`. Follow the
types. Inventory all the arguments and operations available (e.g., `pure`,
`>>=`) with their types and see if you can plug them together like Lego
bricks. You may use do notation if you like, but it's not required.

-/

@[autogradedDef 1]
def map {m : Type → Type} [LawfulMonad m] {α β : Type}
    (f : α → β) (ma : m α) :
    m β :=
  do
    let a ← ma
    pure (f a)

/- (1 point). Prove the identity law for `map`.

Hint: You will need `LawfulMonad.bind_pure`. -/

@[autogradedProof 1]
theorem map_id {m : Type → Type} [LawfulMonad m] {α : Type} (ma : m α) :
    map id ma = ma :=
  by
    simp [map, LawfulMonad.bind_pure]

/- (1 points). Prove the composition law for `map`.
   You'll need `LawfulMonad.bind_assoc` and `LawfulMonad.pure_bind`. -/

@[autogradedProof 2]
theorem map_map {m : Type → Type} [LawfulMonad m] {α β γ : Type}
      (f : α → β) (g : β → γ) (ma : m α) :
    map g (map f ma) = map (fun x ↦ g (f x)) ma :=
  by
    simp [map, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
end Q4_FMap

namespace Q5_ListMonad


/- ## Question 5 (6 points): Monadic Structure on Lists

`List` can be seen as a monad, similar to `Option` but with several possible
outcomes. It is also similar to `Set`, but the results are ordered and finite.
The code below sets `List` up as a monad. -/

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      _ => []
  | a :: as, f => f a ++ bind as f

def pure {α : Type} (a : α) : List α :=
  [a]

/- (1 point). Prove the following property of `bind` under the append
operation. -/

@[autogradedProof 1]
theorem bind_append {α β : Type} (f : α → List β) :
    ∀as as' : List α, bind (as ++ as') f = bind as f ++ bind as' f :=
  by
    intro l_a l_a'
    induction l_a with
      | nil =>
        simp [bind]
      | cons head tail tail_ih =>
        simp [bind, tail_ih]


/- (3 points). Prove the three laws for `List`. -/

-- this one shouldn't need induction
@[autogradedProof 1]
theorem pure_bind {α β : Type} (a : α) (f : α → List β) :
    bind (pure a) f = f a :=
  by
    simp [bind, pure]

@[autogradedProof 1]
theorem bind_pure {α : Type} :
    ∀as : List α, bind as pure = as :=
  by
    intro as
    induction as with
      | nil => simp [bind]
      | cons h t ih =>
        simp [bind, pure]
        exact ih

-- use `bind_append` from above
@[autogradedProof 1]
theorem bind_assoc {α β γ : Type} (f : α → List β) (g : β → List γ) :
    ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) :=
  by
    intro as
    induction as with
    | nil => simp [bind]
    | cons h t ih =>
      simp [bind, bind_append, ih]

/- (1 point). Prove the following list-specific law.

You may find it helpful to do something like `simp [..] at ih` in the inductive case,
 to simplify the induction hypothesis.
 -/

@[autogradedProof 1]
theorem bind_pure_comp_eq_map {α β : Type} {f : α → β} :
    ∀as : List α, bind as (fun a ↦ pure (f a)) = List.map f as :=
  by
    intro as
    induction as with
    | nil => simp [bind]
    | cons h t t_ih =>
      simp [bind, t_ih]
      simp [pure]

/- (1 point). Register `List` as a lawful monad.
   This should be easy, since you have already proved the monad laws.
 -/

@[autogradedDef 1]
instance LawfulMonad : LawfulMonad List :=
  { pure       := pure
    bind       := bind
    pure_bind  := pure_bind
    bind_pure  := bind_pure
    bind_assoc := bind_assoc }

-- Here I'm setting up List as a monad, but only for this namespace.
local instance ListMonad : Monad List :=
  { bind := bind
    pure := pure }

-- Here's a little program to show off the list monad.
-- The list monad can serve as a kind of backtracking search,
-- since it explores all possible combinations of the values drawn from the lists.
def pythagoreanTriples (n : Nat) : List (Nat × Nat × Nat) := do
  let z ← List.range n
  let y ← List.range z
  let x ← List.range y
  -- this point in the program is reached for every triple (x, y, z) such that 0 ≤ x < y < z < n
  -- it's expensive, but you could prune early in other programs
  if x * x + y * y == z * z then
    pure (x, y, z)
  else
    []

#eval pythagoreanTriples 15

end Q5_ListMonad

end LoVe
