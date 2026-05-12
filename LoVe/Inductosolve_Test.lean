/- Test cases for `inductosolve`. Each theorem that compiles = solved.
   Each that fails (errors) = unsolved by current `inductosolve`. -/

import LoVe.LoVe03_BackwardProofs_Demo
import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo
import LoVe.LoVe06_InductivePredicates_Demo
import LoVe.LoVe09_OperationalSemantics_Demo

namespace LoVe
open BackwardProofs

-- ============ LoVe03: arithmetic over ℕ ============

theorem T_mul_zero (n : ℕ) : mul 0 n = 0 := by
  inductosolve? [mul, add]

theorem T_mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n := by
  inductosolve? [mul, add, add_succ, add_assoc]

private theorem mul_zero' (n : ℕ) : mul 0 n = 0 := by
  inductosolve [mul, add]

private theorem mul_succ' (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n := by
  inductosolve [mul, add, add_succ, add_assoc]

theorem T_mul_comm (m n : ℕ) : mul m n = mul n m := by
  inductosolve [mul, mul_zero', mul_succ', add_comm]

theorem T_mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := by
  inductosolve [mul, mul_add]

-- ============ LoVe13: trees (inlined defs) ============

def Tree.graft' {α : Type} : Tree α → Tree α → Tree α
  | Tree.nil,        u => u
  | Tree.node a l r, u => Tree.node a (Tree.graft' l u) (Tree.graft' r u)

theorem T_graft_assoc {α : Type} (t u v : Tree α) :
    Tree.graft' (Tree.graft' t u) v = Tree.graft' t (Tree.graft' u v) := by
  inductosolve [Tree.graft']

theorem T_graft_nil {α : Type} (t : Tree α) :
    Tree.graft' t Tree.nil = t := by
  inductosolve [Tree.graft']

-- ============ LoVe05: lists (drop) — needs custom defs ============

def drop' {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop' m xs

theorem T_drop_nil {α : Type} (n : ℕ) :
    drop' n ([] : List α) = [] := by
  inductosolve [drop']

-- reverseAccu: needs `generalizing` — expected to fail
def reverseAccu' {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu' (x :: as) xs

theorem T_reverseAccu_failing {α : Type} (as xs : List α) :
    reverseAccu' as xs = xs.reverse ++ as := by
  inductosolve [reverseAccu']

-- ============ LoVe06: rule induction on Even — expected to fail ============

theorem T_Even_two_times (m : ℕ) : Even (2 * m) := by
  inductosolve

-- ============ LoVe12: mutual list induction ============

def List_add : List Int → List Int → List Int
  | [],      ys      => ys
  | xs,      []      => xs
  | x :: xs, y :: ys => (x + y) :: List_add xs ys

theorem T_List_add_comm (xs ys : List Int) :
    List_add xs ys = List_add ys xs := by
  inductosolve [List_add]

-- ============================================================
-- Induction proofs extracted from Demo files
-- ============================================================

-- ---- LoVe03 ----
theorem T_demo_add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  inductosolve [add]

-- ---- LoVe04 ----
open ForwardProofs in
theorem T_demo_reverse_append_tactical {α : Type} (xs ys : List α) :
    reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  inductosolve [reverse]

-- ---- LoVe05 ----
theorem T_demo_Nat_succ_neq_self (n : ℕ) : Nat.succ n ≠ n := by
  inductosolve

theorem T_demo_map_eq_list_map {α β : Type} (f : α → β) (xs : List α) :
    map f xs = List.map f xs := by
  inductosolve [map, List.map]

theorem T_demo_map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs := by
  inductosolve [map]

theorem T_demo_map_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    map g (map f xs) = map (g ∘ f) xs := by
  inductosolve? [map]

theorem T_demo_length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) := by
  inductosolve [zip, length, min_add_add]

theorem T_demo_mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t := by
  inductosolve? [mirror]

theorem T_demo_length_listOfVec {α : Type} (n : ℕ) (v : Vec α n) :
    List.length (listOfVec v) = n := by
  inductosolve? [listOfVec, List.length]

-- ---- LoVe06 ----
theorem T_demo_Not_Even_succ (n : ℕ) (ne : Even n) : ¬ Even (n + 1) := by
  inductosolve?

theorem T_demo_mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) : n % 2 = 0 := by
  inductosolve

theorem T_demo_Palindrome_reverse {α : Type} (xs : List α) (hxs : Palindrome xs) :
    Palindrome (reverse xs) := by
  inductosolve [reverse, reverse_append]

theorem T_demo_IsFull_mirror {α : Type} (t : Tree α) (ht : IsFull t) :
    IsFull (mirror t) := by
  inductosolve [mirror, mirror_Eq_nil_Iff]

theorem T_demo_IsFull_mirror_struct {α : Type} (t : Tree α) :
    IsFull t → IsFull (mirror t) := by
  inductosolve? [mirror, mirror_Eq_nil_Iff]

theorem T_demo_Not_Even_two_mul_add_one (m n : ℕ) (hm : m = 2 * n + 1) :
    ¬ Even m := by
  intro h
  inductosolve

theorem T_demo_Star_Star_Iff_Star {α : Type} (R : α → α → Prop) (a b : α) :
    Star (Star R) a b ↔ Star R a b := by
  inductosolve [Star.base, Star.refl, Star.trans]

-- ---- LoVe09 ----
-- BigStep_deterministic, RTC_SmallStep_of_BigStep, SmallStep_final cause
-- whnf timeouts when running inductosolve — the LoVe09 inductive predicates
-- (BigStep, SmallStep) and the Stmt datatype have many constructors which
-- blow up the search space. Skipped to keep the test suite runnable.

theorem T_demo_BigStep_of_SmallStep_of_BigStep {Ss₀ Ss₁ s₂} (h₁ : Ss₀ ⇒ Ss₁) :
    Ss₁ ⇓ s₂ → Ss₀ ⇓ s₂ := by
  inductosolve [BigStep_while_true_Iff]

-- ---- LoVe10 ----
-- Skipped: LoVe10_HoareLogic_Demo has a pre-existing compile failure
-- (unrelated to inductosolve).

end LoVe
