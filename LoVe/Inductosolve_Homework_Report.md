# Inductosolve coverage report — Homework

Survey of every induction problem in `Homework/Homework{1,2,3,4}.lean`. Tests
live in `LoVe/Inductosolve_Homework_Test.lean` (definitions copied since
`Homework/` isn't a lake library).

## ✅ Solvable (11)

All tested and confirmed passing.

| Theorem | HW | Invocation | Notes |
|---|---|---|---|
| `sum_snoc` | HW2 Q6 | `inductosolve [sum, snoc]` | Standard list induction; closer's `simp_all [sum, snoc]; ac_rfl` closes the cons case (matches the hand-written proof exactly). |
| `sum_append` | HW2 Q6 | `inductosolve [sum]` | List induction; `simp_all + ac_rfl` handles the cons case. |
| `sum_reverse` | HW2 Q6 | `inductosolve [sum, reverse, T_sum_snoc]` | Uses the prior `sum_snoc` lemma. |
| `Even_Not_Odd` | HW3 Q1.4 | `inductosolve` (no lemmas) | **Surprise pass**: aesop handles the rule-induction-shaped negation without explicit `Even`/`Odd` lemmas. |
| `sumUpToOfFun_mul` | HW3 Q2 | `inductosolve [sumUpToOfFun]` | Nat induction, succ case is linear. |
| `Subseq_empty` | HW3 Q3 | `inductosolve [Subseq.rfl, Subseq.drop]` | List induction; closer applies the constructor lemmas. |
| `Subseq_concat_same` | HW3 Q3 | `inductosolve [Subseq.keep]` | List induction on `xs`. |
| `bind_append` | HW3 Q5 | `inductosolve [bind]` | List induction. |
| `bind_pure` | HW3 Q5 | `inductosolve [bind, pure]` | List induction. |
| `bind_assoc` | HW3 Q5 | `inductosolve [bind, bind_append]` | List induction, reuses `bind_append`. |
| `bind_pure_comp_eq_map` | HW3 Q5 | `inductosolve [bind, pure]` | List induction. |

## ❌ Not solvable (6 confirmed by test + ~7 predicted)

### Confirmed failures

| Theorem | HW | Why | Class |
|---|---|---|---|
| `Odd_Even` | HW3 Q1.3 | `Odd n → Even (n+1)` requires induction on the `Odd` derivation, not on `n`. Our tactic only inducts on data, not on inductive-predicate hypotheses. | Rule induction on predicate. |
| `Even_add` | HW3 Q1.5 | `Even m → Even n → Even (m+n)`. Needs rule induction on the `Even m` hypothesis. | Rule induction on predicate. |
| `Even_mul_two` | HW3 Q1.5 | Nat induction works *structurally* but the succ case needs `Even.add_two` applied to the IH, plus `Nat.mul_comm/mul_add` rewriting. Our closer's `simp_all`/`aesop` couldn't find the path. | Branch closer too weak. |
| `Even_mul_even` | HW3 Q1.5 | Same shape as `Even_add` — rule induction on `Even m`. | Rule induction. |
| `sumUpToOfFun_eq` | HW3 Q2 | Nat induction works; succ case reduces to `2 * (S n + (n+1)) = (n+1) * (n+2)` — needs `linarith` / `ring`. Our closer doesn't include them. | Branch closer missing `linarith`. |
| `Subseq_empty_iff_empty` | HW3 Q3 | Iff statement; one direction needs case-split on `xs` *and* inversion of `Subseq xs []`. Our tactic doesn't split iff goals nor inverts inductive relations. | Iff + relation inversion. |

### Predicted failures (not tested, predictions based on structure)

| Theorem | HW | Why |
|---|---|---|
| `Subseq_concat` | HW3 Q3 | Rule induction on `Subseq a' a`. |
| `Eval_type_sound` | HW4 Q1 | Rule induction on `HasType`, with hundreds of lines of `obtain`/`cases` per branch. Far beyond closer scope. |
| `finset_zero_add` | HW4 Q2 | Uses `induction x using Quotient.inductionOn` — custom induction principle our tactic doesn't dispatch. |
| `finset_add_comm` | HW4 Q2 | Double `Quotient.inductionOn`. |
| `finset_add_assoc` | HW4 Q2 | Triple `Quotient.inductionOn`. |
| `finset_add_zero` | HW4 Q2 | `Quotient.inductionOn`. |
| HW1 Q3 statements | HW1 | Stated as `sorry`; the proofs are the same as HW2 Q6 (same `sum_snoc/append/reverse`) and would pass with the same invocations. |

## Patterns by homework

| Homework | Induction problems | Solvable by inductosolve | Coverage |
|---|---|---|---|
| HW1 | 3 (statements only) | 3 (same as HW2 Q6) | 100% |
| HW2 | 3 (`sum_snoc`, `sum_append`, `sum_reverse`) | 3 | **100%** |
| HW3 | 13 | 7 confirmed solvable + 6 fail | **54%** |
| HW4 | 6 (`Eval_type_sound`, 4× `finset_*`, plus `HasType_Incomplete` non-induction) | 0 | **0%** |
| **Overall** | **25** | **13** | **~52%** |

## What the data says about `inductosolve`

**Strong**: clean structural induction on `List`/`Nat` with simp-closable branches. HW2 is a perfect fit, and most of HW3 Q5 (list monad laws) lands here.

**Weak**: anything that the hand-written proof opens with `induction <hypothesis>` instead of `induction <data var>`. The Even/Odd theorems in HW3 Q1 and the `Subseq_concat` / `Eval_type_sound` theorems all use rule induction on inductive predicates — a fundamentally different operation our tactic doesn't implement.

**Specific to HW3 Q2 (`sumUpToOfFun_eq`)**: this is the cheapest near-miss. Adding `linarith` or `ring` to the closer's `first |` chain would close it; the user's reference proof literally is `simp [sumUpToOfFun]; rw [Nat.mul_add, ih]; linarith`.

**Specific to HW4**: the `Quotient.inductionOn` cases need `inductosolve` to accept a `using` clause (mirroring Lean's `induction x using f` syntax). Easy syntax extension; would unlock all four `finset_*` theorems.

## Concrete next features (ranked by ROI)

1. **`linarith` / `ring` / `omega` in the closer** — one-line change to `branch_solve`, unlocks `sumUpToOfFun_eq` and likely `Even_mul_two`.
2. **`induction x using <principle>` syntax** — accept `inductosolve x using Quotient.inductionOn [defs]`. Unlocks all HW4 Q2 problems.
3. **Rule induction on an inductive-predicate hypothesis** — would need to detect `Even`/`Odd`/`Subseq` hypotheses and try `induction h` on them (where `h : Even n`). Unlocks `Odd_Even`, `Even_add`, `Even_mul_even`, `Subseq_concat`.
4. **`generalizing` clause** (carried over from the ExerciseSheet report) — accumulator-style proofs.
