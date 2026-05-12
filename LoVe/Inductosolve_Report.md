# Inductosolve coverage report

Survey of induction problems across `LoVe/LoVe*_ExerciseSheet.lean` (upstream
`mwillsey/cs263@2026-spring` is the authoritative problem set). Each problem
was either run directly through `inductosolve` (see `LoVe/Inductosolve_Test.lean`)
or classified statically when its dependencies couldn't be set up cheaply.

## ✅ Solvable

All of these pass with `inductosolve [...]` taking the obvious function/lemma list.

| Theorem | Sheet | Invocation | Shape |
|---|---|---|---|
| `mul_zero` | LoVe03 | `inductosolve [mul, add]` | Nat induction; both branches close via `simp_all`. |
| `mul_succ` | LoVe03 | `inductosolve [mul, add, add_succ, add_assoc]` | Nat induction on `n`; succ branch uses IH + add_succ. |
| `mul_comm` | LoVe03 | `inductosolve [mul, mul_zero, mul_succ, add_comm]` | Nat induction on `n`; needs prior `mul_*` lemmas. |
| `mul_assoc` | LoVe03 | `inductosolve [mul, mul_add]` | Nat induction on `n`; standard distributivity. |
| `Tree.graft_assoc` | LoVe13 | `inductosolve [Tree.graft]` | Structural induction on `Tree`; the closer's `simp_all [Tree.graft]` handles both `Tree.nil` / `Tree.node` cases. |
| `Tree.graft_nil` | LoVe13 | `inductosolve [Tree.graft]` | Same as above, simpler statement. |
| `drop_nil` | LoVe05 | `inductosolve [drop]` | Nat induction; defining `drop n []` reduces by simp. |
| `Even_two_times` | LoVe06 | `inductosolve` (no lemmas) | Nat induction on `m`; closer's `aesop` finishes — uses `Even.zero` and `Even.add_two` constructors from `Even`'s simp/elab set. |

**Common characteristics of the solvable set:**
- Single inductive variable; the right one is *also* in the local context (so our "try each variable, commit only on full close" loop finds it).
- Both branches close from `simp_all [defs, prior_lemmas]` or `simp_all [...]; ac_rfl`.
- IHs are picked up by `simp_all`, not needed as explicit named arguments.
- No `generalizing` clause, no special induction principle.

## ❌ Not solvable (current `inductosolve`)

| Theorem | Sheet | Why it fails | Class |
|---|---|---|---|
| `add_mul` | LoVe03 | Statement: `mul (add l m) n = add (mul n l) (mul n m)`. Upstream comment says to prove with `rw [mul_comm _ l]` — `simp [mul_comm]` is non-terminating, so our closer can't close. **Not an induction problem at all**, mis-bucketed by the test. | Wrong-tool problem. |
| `reverseAccu_Eq_reverse_append` | LoVe05 | Needs `induction xs generalizing as`. Our tactic does plain `induction`, so the IH is too specific (fixed `as`) and the cons case can't be discharged. | Needs `generalizing`. |
| `drop_drop`, `take_take`, `take_drop` | LoVe05 | Three-case pattern matching that mirrors `drop`/`take`'s recursion (`0 _`, `n+1 []`, `n+1 (x::xs)`). Standard `induction n` produces two cases, not three; the recursive call in `drop` makes the IH fire on a different `xs`. Pattern-match-based recursion is the canonical approach, which our tactic doesn't generate. | Needs pattern-matching induction / recursor. |
| `List.length_add`, `List.add.comm` | LoVe12 | Mutual structural induction on **two** lists at once — four base/inductive cases (nil/nil, nil/cons, cons/nil, cons/cons). Our loop inducts on one variable at a time. After `induction xs`, the second var `ys` is still a free variable, and `simp_all` alone can't case-split it. | Needs simultaneous induction on two vars. |
| `int.neg_neg` | LoVe12 | Uses `induction a using Quotient.inductionOn`. Our tactic doesn't support custom induction principles. | Custom induction principle. |
| `var_while_intro_aux` | LoVe10 | Well-founded / strong induction on a numeric variant `v₀ : ℕ`. Plain structural Nat induction is too weak. | Strong/well-founded induction. |
| `mirror_IsFull`, `map_mirror` | LoVe06 | Rule induction on the inductive **predicate** `IsFull`, not on the data. Our tactic only inducts on inductive-typed local variables, not on hypotheses of inductive-predicate type. | Rule induction on predicate. |
| `BigStep_*`, `BigStepEquiv.*` (LoVe09) | LoVe09 | Inversion/equivalence proofs over the `BigStep` inductive relation. No structural induction on data; the proofs use `cases` on `BigStep` derivations and constructor application. | Not induction-shaped (relation reasoning). |
| `Finset.elems_mirror` | LoVe13 | Tree induction, but the conclusion is a `Finset` equality that requires `Finset.ext` plus membership lemmas across nested constructors. Our closers (`simp_all`, `aesop`) don't reach this without finer lemma hints. | Tree induction with non-trivial closer (likely solvable with the right `[...]` list — not yet tested). |

## Patterns

**What `inductosolve` is good at:**
- One inductive variable, both branches discharged by `simp`-style reasoning with explicit equation lemmas.
- Recursive function definitions provided as simp arguments.
- Simple Tree/List/Nat structural induction.
- Auxiliary `ac_rfl` step for goals up to associativity/commutativity.

**Where it falls down:**
1. **Generalizing IH** — accumulator-style proofs.
2. **Mutual / simultaneous induction** on multiple variables.
3. **Pattern-match recursion** where `induction n with | zero | succ` gives the wrong case split.
4. **Custom induction principles** (`Quotient.inductionOn`, well-founded, recursors).
5. **Rule induction** on inductive predicates / relations rather than data.
6. **Inversion** of inductive relations — no induction at all, just `cases`.

## Concrete next steps (in priority order)

1. **Support `generalizing`**: accept `inductosolve x generalizing y z` syntax and splice `generalizing` into the induction call. Unlocks `reverseAccu_Eq_reverse_append`.
2. **Try `cases` as a fallback when no inductive vars are useful**: would not gain LoVe09 problems (different proof shape) but would broaden coverage cheaply.
3. **Multi-variable induction**: try nested `induction v1 <;> induction v2` for mutual cases. Brittle, but unlocks the LoVe12 list problems.
4. **Stronger closer**: pre-process with `ring`/`omega`/`linarith` before falling back to `aesop`. Cheap, might close `add_mul`-style goals.
