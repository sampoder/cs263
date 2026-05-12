/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe Exercise 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check Vector

/- The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer list is ignored. -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. Show that if the lists have the same length, the resulting list also
has that length. -/

theorem List.length_add :
    ∀xs ys, List.length xs = List.length ys →
      List.length (List.add xs ys) = List.length xs
  | [], [] =>
    by simp [List.add]
  | x :: xs, y :: ys =>
    by
      simp [List.add]
      apply List.length_add
  | [], y :: ys =>
    by simp [List.add]
  | x :: xs, [] =>
    by simp [List.add]

/- 1.2. Define componentwise addition on vectors using `List.add` and
`List.length_add`. -/

def Vector.add {n : ℕ} (a: Vector ℤ n) (b: Vector ℤ n) : Vector ℤ n :=
  Subtype.mk (List.add a.val b.val)
    (by simp [List.length_add, a.property, b.property];)

def Vector.wack_add {n : ℕ} : Vector ℤ n → Vector ℤ n → Vector ℤ n :=
  fun a b ↦ {
    val := List.add a.val b.val
    property := by simp [List.length_add, a.property, b.property]
  }


/- 1.3. Show that `List.add` and `Vector.add` are commutative. -/

theorem List.add.comm :
    ∀xs ys, List.add xs ys = List.add ys xs
  | [], [] =>
    by simp [List.add]
  | x :: xs, y :: ys =>
    by
      simp [List.add, add_comm]
      apply List.add.comm
  | [], y :: ys =>
    by simp [List.add]
  | x :: xs, [] =>
    by simp [List.add]



theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
    Vector.add u v = Vector.add v u :=
  by simp [List.add.comm, Vector.add]


/- ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `Int` (= `ℤ`): -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. Define negation on these integers. Observe that if `(p, n)` represents
an integer, then `(n, p)` represents its negation. -/

def Int.neg : Int → Int :=
  Quotient.lift
    (fun a : ℕ × ℕ ↦ ⟦(Prod.snd a, Prod.fst a)⟧)
    (by
      intro a b c
      simp
      apply Quotient.sound
      rw [Int.Setoid_Iff] at *
      linarith
      )

/- 2.2. Prove the following theorems about negation. -/

theorem Int.neg_eq (p n : ℕ) :
    Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
  by
    simp [Int.neg]

theorem int.neg_neg (a : Int) :
    Int.neg (Int.neg a) = a :=
  by
    induction a using Quotient.inductionOn with
    | h pn =>
      cases pn with
        | mk p n => simp [Int.neg]


/- ## Question 3: Multisets as Quotients

We can encode finite multisets (bags) as lists quotiented by permutation:
two lists represent the same multiset if one is a permutation of the other.

3.1. Define the setoid and quotient type. -/

instance MSet.Setoid (α : Type) : Setoid (List α) :=
  { r := List.Perm
    iseqv :=
      { refl := List.Perm.refl
        symm := List.Perm.symm
        trans := List.Perm.trans } }

def MSet (α : Type) : Type :=
  Quotient (MSet.Setoid α)

/- 3.2. Define multiset union as list concatenation on representatives.
You must show this is well defined with respect to permutations. -/

-- this will be helpful
#check List.Perm.append

def MSet.union {α : Type} : MSet α → MSet α → MSet α :=
  Quotient.lift₂
    (fun xs ys : List α ↦ (⟦xs ++ ys⟧ : MSet α))
    (by
       intro xs₁ xs₂ ys₁ ys₂ hxs hys
       -- You'll probably need to apply quotient soundess here.
       simp
       apply Quotient.sound
       apply List.Perm.append hxs hys
       )

/- 3.3. Prove the computation rule for concrete representatives. -/

theorem MSet.union_Eq {α : Type} (xs ys : List α) :
    MSet.union (⟦xs⟧ : MSet α) (⟦ys⟧ : MSet α) =
    (⟦xs ++ ys⟧ : MSet α) :=
  by
    rfl

end LoVe
