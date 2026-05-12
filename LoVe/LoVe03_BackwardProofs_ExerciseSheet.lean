/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a :=
  by
    intro ha
    exact ha

theorem K (a b : Prop) :
    a → b → b :=
  by
    intro ha
    intro hb
    exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by
    intro hf
    intro hb
    intro ha
    exact hf ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  by
    intro ha
    intro hb
    exact ha

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  by
    intro ha
    intro hb
    exact hb

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intro habc
    intro ha
    intro hac
    intro hb
    apply hac ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intro hab
    intro hnb
    intro ha
    apply hnb
    apply hab ha






/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    . intro f
      apply And.intro
      . intro y
        exact(f y).left
      . intro z
        exact(f z).right
    . intro fand
      intro y
      apply And.intro
      . exact fand.left y
      . exact fand.right y

/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  by
    induction n
    . rfl
    . rw [mul]
      rw [a]
      rfl

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n
    . simp [mul, add]
    . simp [mul, add, a, add_succ, add_assoc]






/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  by
    induction n
    . simp [mul, mul_zero]
    . simp [mul, mul_succ, add_comm, a]

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  by
    inductosolve
    induction n
    . simp [mul]
    . simp [mul, a, mul_add]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) :=
  by
    simp [mul_comm, mul_add]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

#check Or.elim

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  by
    unfold ExcludedMiddle
    unfold Peirce
    intro a
    intro b
    intro c
    intro d
    apply Or.elim (a b)
    { exact id }
    {
      intro nb
      apply d
      intro ha
      apply False.elim
      exact nb ha

    }


/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  by
    unfold Peirce
    unfold DoubleNegation
    intro p
    intro a
    intro nna
    apply p a False
    intro f
    apply False.elim
    rw [←Not] at f
    exact nna f

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  sorry

end SorryTheorems

end BackwardProofs

end LoVe
