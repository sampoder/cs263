/-
# Inductosolve

A tactic that tries to discharge induction-shaped proof goals automatically.

Usage:
  `inductosolve`              — black-box: silently closes the goal if it can
  `inductosolve?`             — white-box: closes AND emits a `Try this: …`
                                suggestion containing the explicit tactic
                                chain that worked
  `inductosolve [foo, bar]`   — pass hint lemmas (works with `?` too)

## Black-box vs white-box

`inductosolve` succeeds silently — the user has no insight into what worked.
`inductosolve?` (suffix-style, mirroring `aesop?`, `simp?`, `exact?`) emits
a `Try this:` suggestion showing the underlying explicit tactic chain. The
user can click it in the IDE to replace `inductosolve?` with the concrete
proof — making the proof robust to future changes in this tactic.

## How it works (high level)

1. Build a goal-closer `closeBranch` — a `first | …` chain of cheap tactics
   (rfl, ac_rfl, simp_all, aesop, …) extended with `apply <ctor>` for any
   inductive predicates that appear in the goal.
2. Scan the local context to find inductive-typed local variables, split
   into *predicate* hypotheses (`h : Even n`) and *data* variables (`n : ℕ`).
3. Try a sequence of induction strategies. Each strategy is wrapped in
   `solve | …`, so a partial result is rolled back and we move on:
     a. `closeBranch` alone (no induction).
     b. plain `induction v` on each var.
     c. induction + `intro; cases` on each branch.
     c'. predicate induction with `generalizing`.
     d. `induction v generalizing <other same-typed vars>`.
     e. mutual induction (`induction v generalizing w <;> induction w`).
     f. cases-based variant of (e) (`<;> intros <;> cases w`).
4. If nothing fully closes the goal, do a best-effort `induction <first var>`
   with `try closeBranch` per branch — leaves a partial proof state for the
   user.
-/

import Lean
import Aesop
import Mathlib.Tactic.Linarith
import Lean.Meta.Tactic.TryThis

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

namespace LoVe

/-- Does the (telescoped) result type of `expr` end in `Prop`?

Used to distinguish inductive **predicates** (whose type ends in `Prop` —
e.g. `Even : ℕ → Prop`) from inductive **data types** (whose type ends in
`Type` — e.g. `Nat`, `List α`, `Tree α`). Predicates get rule induction;
data vars get structural induction. -/
private partial def resultIsProp : Expr → Bool
  | .forallE _ _ body _ => resultIsProp body
  | result              => result.isProp

/-- Strip leading `∀`/`→` from an expression, returning the conclusion.

Used when scanning the goal for relevant inductive predicates: we only
want to consider the conclusion, not the antecedents (those would bring
in unrelated predicates and blow up the search). -/
private partial def stripForalls : Expr → Expr
  | .forallE _ _ body _ => stripForalls body
  | conclusion          => conclusion

-- Surface syntax. Two near-identical tactics: one silent, one that emits
-- a `Try this:` suggestion (the white-box variant).
syntax (name := inductosolve)         "inductosolve"  (" [" ident,* "]")? : tactic
syntax (name := inductosolveSuggest)  "inductosolve?" (" [" ident,* "]")? : tactic

/-- Main implementation of `inductosolve`.

* `suggest`     — if `true`, emit a `Try this:` suggestion on success
                  containing the underlying explicit tactic chain.
* `hintLemmas`  — user-provided identifiers (passed via the optional
                  `[…]` clause). Spliced into `simp_all` / `simp only` calls
                  and used as `apply` targets where appropriate. -/
private def runInductosolve (suggest : Bool) (hintLemmas : Array Ident) :
    TacticM Unit :=
  withMainContext do
    let localCtx    ← Lean.MonadLCtx.getLCtx
    let environment ← getEnv

    -- ===== Step 1: build the per-branch closer =====
    -- `closeBranch` is what we run on each subgoal produced by `induction`.
    -- A `first | …` chain in two flavors (with/without hint lemmas) where
    -- each alternative either fully closes the branch (ending in `done`,
    -- `rfl`, `ac_rfl`, `linarith`, `aesop`/`aesop?`, …) or fails.
    --
    -- We always use plain `aesop` (silent) in the closer. Using `aesop?`
    -- would emit a *second* `Try this:` whenever aesop fires, creating
    -- two stacked suggestions at the call site (confusing UX). We emit
    -- exactly one suggestion ourselves; if the user wants aesop's
    -- concrete trace, they can edit the pasted suggestion and change
    -- `aesop` to `aesop?` manually.
    let aesopTac ← `(tactic| aesop)
    let closeBranch ←
      if hintLemmas.isEmpty then
        `(tactic| (first
          -- Trivial closers, cheap to try first.
          | rfl
          | ac_rfl
          | assumption
          | linarith
          -- Implication goals: intro then close.
          | (intros; contradiction)
          | (intros; rfl)
          | (intros; assumption)
          -- Simp-based closers. `done` asserts no goals remain after simp.
          | (simp_all; done)
          | (simp; done)
          | (simp_all; ac_rfl)
          | (simp; ac_rfl)
          | (simp_all; linarith)
          | (simp; linarith)
          | (simp_all; assumption)
          | (intros; simp_all; done)
          -- Heavyweight search as last resort.
          | $aesopTac:tactic))
      else
        `(tactic| (first
          | rfl
          | ac_rfl
          | assumption
          | linarith
          | (intros; contradiction)
          | (intros; rfl)
          | (intros; assumption)
          -- The same simp/aesop chain, but spliced with the user's hints
          -- so simp can use them as rewrite rules.
          | (simp_all [$[$hintLemmas:term],*]; done)
          | (simp     [$[$hintLemmas:term],*]; done)
          | (simp_all [$[$hintLemmas:term],*]; ac_rfl)
          | (simp     [$[$hintLemmas:term],*]; ac_rfl)
          | (simp_all [$[$hintLemmas:term],*]; linarith)
          | (simp     [$[$hintLemmas:term],*]; linarith)
          | (simp_all [$[$hintLemmas:term],*]; assumption)
          | (intros; simp_all [$[$hintLemmas:term],*]; done)
          | ((try simp only [$[$hintLemmas:term],*]); $aesopTac:tactic)
          | $aesopTac:tactic))

    -- ===== Step 2: classify local inductive vars =====
    -- Walk the local context and bucket each inductive-typed local decl as
    -- either:
    --   • a *predicate* (its type ends in `Prop`, e.g. `h : Even n`), or
    --   • a *data var* (its type ends in `Type`, e.g. `n : ℕ`).
    -- For data vars we also remember the head constructor name so we can
    -- later compare "same-typed" pairs (e.g. two `List _` vars even if their
    -- element types differ).
    let (predicateHyps, dataVars) ← localCtx.foldlM
      (init := ((#[] : Array Ident), (#[] : Array (Ident × Name))))
      fun (predicateHyps, dataVars) decl => do
        let typeHead := decl.type.getAppFn
        if let .const headName _ := typeHead then
          if let some (.inductInfo inductiveInfo) := environment.find? headName then
            let varIdent := mkIdent decl.userName
            if resultIsProp inductiveInfo.type then
              return (predicateHyps.push varIdent, dataVars)
            else
              return (predicateHyps, dataVars.push (varIdent, headName))
        return (predicateHyps, dataVars)
    let dataVarIds        := dataVars.map Prod.fst
    -- The full ordered list of induction-candidate vars: predicates first
    -- (rule induction on a hypothesis usually wins when one is present),
    -- then data vars.
    let allInductiveVars  := predicateHyps ++ dataVarIds

    -- ===== Step 3: gather predicate constructors for the closer =====
    -- For each inductive predicate appearing in the goal's *conclusion*
    -- (we skip antecedents to avoid pulling in unrelated predicates), add
    -- `apply <constructor>` alternatives to the closer. This lets the
    -- closer take one constructor "step" — e.g. `Even 2` becomes `Even 0`
    -- after `apply Even.add_two`, which a later closer alt then handles.
    let goalType ← instantiateMVars (← getMainTarget)
    let collectPredicateHead : Expr → NameSet → NameSet := fun expr acc =>
      if let .const headName _ := expr.getAppFn then
        match environment.find? headName with
        | some (.inductInfo info) =>
          if resultIsProp info.type then acc.insert headName else acc
        | _ => acc
      else acc
    let goalPredicateNames := collectPredicateHead (stripForalls goalType) {}

    -- Tally total constructors across the relevant predicates. If it's
    -- large (think `BigStep` with 7 ctors), the depth-2 constructor-apply
    -- expansion creates a syntax tree of size ~ctors², which `whnf`
    -- times out on. Drop the ctor extension in that case — the rest of
    -- the closer (simp / aesop) still runs.
    let totalCtors : Nat := Id.run do
      let mut total := 0
      for predName in goalPredicateNames do
        if let some (.inductInfo info) := environment.find? predName then
          total := total + info.ctors.length
      pure total
    let useCtorAlts := totalCtors ≤ 4

    -- Helper: given an `inner` closer, return a list of `apply <ctor>`
    -- alternatives wrapping `inner` (the constructor is applied first, then
    -- `inner` runs on every resulting subgoal). Wrapped in `solve |` so an
    -- application that lands on a wrong constructor (right shape, wrong
    -- meaning) backtracks instead of leaving stray subgoals.
    let makeConstructorAlternatives (inner : TSyntax `tactic) :
        TacticM (Array (TSyntax `tactic)) := do
      if !useCtorAlts then return #[]
      let mut alternatives : Array (TSyntax `tactic) := #[]
      for predicateName in goalPredicateNames do
        if let some (.inductInfo inductiveInfo) := environment.find? predicateName then
          for constructorName in inductiveInfo.ctors do
            let constructorIdent := mkIdent constructorName
            alternatives := alternatives.push
              (← `(tactic| solve | (apply $constructorIdent <;> $inner:tactic)))
            -- Also try a simp_all rewrite before applying — the goal may
            -- have a non-canonical form (e.g. `(n+1)*2` instead of `?+2`)
            -- that blocks the bare `apply`.
            if !hintLemmas.isEmpty then
              alternatives := alternatives.push
                (← `(tactic| solve |
                  ((try simp_all [$[$hintLemmas:term],*]);
                   apply $constructorIdent <;> $inner:tactic)))
      pure alternatives

    let wrapWithConstructorAlts (inner : TSyntax `tactic) :
        TacticM (TSyntax `tactic) := do
      let alternatives ← makeConstructorAlternatives inner
      if alternatives.isEmpty then pure inner
      else `(tactic| (first $[| $alternatives:tactic]* | $inner:tactic))

    -- Apply two layers of constructor extensions so the closer can chain
    -- up to two constructor applications in sequence (e.g. proving `Even 2`
    -- needs `apply Even.add_two; apply Even.zero`).
    let closeBranchDepth1 ← wrapWithConstructorAlts closeBranch
    let closeBranch       ← wrapWithConstructorAlts closeBranchDepth1

    -- A compact, user-readable proxy for `closeBranch`, used only in
    -- `Try this:` suggestions. The real closer is a many-alt `first | …`
    -- tree which pretty-prints into an unreadable blob; emitting a
    -- canonical short form gives the user a starting point they can tweak.
    -- Must include the *finisher* alternatives that `closeBranch` uses
    -- (`ac_rfl`, `linarith`) — without them, pasted suggestions for proofs
    -- whose last step is arithmetic/commutativity (e.g. cons/cons branch
    -- of `List_add_comm` leaving `a + b = b + a`) fail to compile.
    let suggestionCloser ←
      if hintLemmas.isEmpty then
        `(tactic| (first
          | rfl
          | ac_rfl
          | linarith
          | (simp_all; done)
          | (simp_all; ac_rfl)
          | (simp_all; linarith)
          | aesop))
      else
        `(tactic| (first
          | rfl
          | ac_rfl
          | linarith
          | (simp_all [$[$hintLemmas:term],*]; done)
          | (simp_all [$[$hintLemmas:term],*]; ac_rfl)
          | (simp_all [$[$hintLemmas:term],*]; linarith)
          | aesop))

    -- ===== White-box machinery =====
    -- `tryStrategy` takes two attempts:
    --   • `full`     — the heavy closer (the big `first | …` chain). Likely
    --                  to succeed but pretty-prints into a blob.
    --   • `compact`  — `suggestionCloser` in place of the full closer.
    --                  Contains `aesop?` which emits its own `Try this:`
    --                  with the concrete proof aesop found.
    -- In **silent** mode (`inductosolve`), we just run `full` — fastest.
    -- In **suggest** mode (`inductosolve?`), we try `compact` first so its
    -- embedded `aesop?` actually fires (giving the user the literal proof,
    -- not just the text "aesop?"). If `compact` fails, fall back to `full`.
    -- Either way, on success we emit `compact` as our own `Try this:`.
    let outerRef ← getRef

    -- Per-branch capture: run `induction v`, then on each resulting branch
    -- run aesop? in isolation, scrape its `Try this:` message text, and
    -- reassemble into `induction v with | <case₁> => <proof₁> | …`. If
    -- aesop fails on any branch we abort (return `none`) and the caller
    -- falls back to the simpler suggestion form.
    -- `preBranch?` is an optional `(tactic, label)` to run BEFORE each
    -- candidate per branch — and prepend to the inlined branch label. Used
    -- by Strategy 4c, which closes branches via `intro h <;> cases h <;>
    -- <closer>`; we need the same `intro h <;> cases h` in front of each
    -- candidate (and in the captured aesop? text) so the branch state
    -- matches what the strategy actually faces.
    let captureInductionProof (inductionVar : Ident)
        (preBranch? : Option (TSyntax `tactic × String) := none) :
        TacticM (Option String) := do
      let snapshot ← saveState
      try
        evalTactic (← `(tactic| induction $inductionVar:term))
        let branchGoals ← getUnsolvedGoals
        let mut parts : Array String := #[]
        for branchGoal in branchGoals do
          let tagName ← branchGoal.getTag
          let branchSnapshot ← saveState
          setGoals [branchGoal]
          let logBefore ← Core.getMessageLog
          Core.setMessageLog {}
          let mut capturedProof? : Option String := none
          -- Run the same per-branch closer the user would write — simp_all
          -- with their hints first, then `aesop?` so any aesop step gets
          -- inlined. Only the aesop? path produces a `Try this:`; the
          -- simp_all path closes silently, in which case we synthesize a
          -- `simp_all [hints]` suggestion ourselves.
          -- Build a list of candidate per-branch closer tactics. We try
          -- each in turn; the first that closes the branch wins, and its
          -- name becomes the inlined proof text. Naming a tactic up-front
          -- (rather than scraping a `Try this:` message) lets us inline
          -- everything from simp variants to constructor applications.
          let simpHints := if hintLemmas.isEmpty then "" else
            " [" ++ String.intercalate ", "
              (hintLemmas.toList.map (·.getId.toString)) ++ "]"
          let mut candidates : Array (TSyntax `tactic × String) := #[]
          candidates := candidates.push ((← `(tactic| rfl)), "rfl")
          candidates := candidates.push ((← `(tactic| assumption)), "assumption")
          let simpAll ←
            if hintLemmas.isEmpty then `(tactic| (simp_all; done))
            else `(tactic| (simp_all [$[$hintLemmas:term],*]; done))
          candidates := candidates.push (simpAll, s!"simp_all{simpHints}")
          -- Simp variants that handle the "simp + arithmetic finish" pattern.
          let simpAllAc ←
            if hintLemmas.isEmpty then `(tactic| (simp_all; ac_rfl))
            else `(tactic| (simp_all [$[$hintLemmas:term],*]; ac_rfl))
          candidates := candidates.push (simpAllAc, s!"simp_all{simpHints}; ac_rfl")
          let simpAllLin ←
            if hintLemmas.isEmpty then `(tactic| (simp_all; linarith))
            else `(tactic| (simp_all [$[$hintLemmas:term],*]; linarith))
          candidates := candidates.push (simpAllLin, s!"simp_all{simpHints}; linarith")
          let simpAllAsm ←
            if hintLemmas.isEmpty then `(tactic| (simp_all; assumption))
            else `(tactic| (simp_all [$[$hintLemmas:term],*]; assumption))
          candidates := candidates.push (simpAllAsm, s!"simp_all{simpHints}; assumption")
          -- Constructor-apply (depth-1): `apply <ctor>` then close.
          for predicateName in goalPredicateNames do
            if let some (.inductInfo info) := environment.find? predicateName then
              for ctor in info.ctors do
                let ctorIdent := mkIdent ctor
                let inner ←
                  if hintLemmas.isEmpty then
                    `(tactic| (first | rfl | assumption | (simp_all; done) | aesop))
                  else
                    `(tactic| (first | rfl | assumption | (simp_all [$[$hintLemmas:term],*]; done) | aesop))
                candidates := candidates.push
                  ((← `(tactic| (apply $ctorIdent <;> $inner:tactic))),
                   s!"apply {ctor} <;> assumption")
                -- Same pattern but with a `simp_all [hints]` *first*. Needed
                -- when the goal's surface form (e.g. `Even (0 * 2)`) blocks
                -- `apply <ctor>` from unifying; simp rewrites first into a
                -- canonical shape (`Even 0`) that the ctor matches.
                if !hintLemmas.isEmpty then
                  let cand ←
                    `(tactic| ((try simp_all [$[$hintLemmas:term],*]);
                               apply $ctorIdent <;> (first | rfl | assumption | aesop)))
                  candidates := candidates.push
                    (cand, s!"simp_all{simpHints}; apply {ctor} <;> assumption")
          -- Depth-2 constructor apply: needed for things like `Even 2`.
          for predicateName in goalPredicateNames do
            if let some (.inductInfo info1) := environment.find? predicateName then
              for ctor1 in info1.ctors do
                let c1 := mkIdent ctor1
                for predicateName2 in goalPredicateNames do
                  if let some (.inductInfo info2) := environment.find? predicateName2 then
                    for ctor2 in info2.ctors do
                      let c2 := mkIdent ctor2
                      let cand ←
                        `(tactic| (apply $c1 <;> apply $c2 <;> (first | rfl | assumption)))
                      candidates := candidates.push (cand, s!"apply {ctor1}; apply {ctor2}")

          for (cand, label) in candidates do
            if capturedProof?.isSome then break
            let candSnapshot ← saveState
            -- If there's a pre-branch tactic, run it first (via `<;>`) so
            -- the candidate closes whatever subgoals it produces.
            let (effectiveCand, effectiveLabel) ← match preBranch? with
              | some (pre, preLabel) =>
                pure ((← `(tactic| ($pre:tactic <;> $cand:tactic))),
                      s!"{preLabel} <;> {label}")
              | none => pure (cand, label)
            try
              evalTactic effectiveCand
              if (← getUnsolvedGoals).isEmpty then
                capturedProof? := some effectiveLabel
              else
                candSnapshot.restore
            catch _ => candSnapshot.restore

          -- Last resort: run `aesop?` and scrape its `Try this:` message to
          -- get the concrete proof aesop found (not just the literal word
          -- "aesop"). Done last so the cheaper named candidates win when
          -- they apply. If there's a pre-branch tactic, wrap with `<;>`
          -- and prefix the scraped label.
          if capturedProof?.isNone then
            let aesopSnapshot ← saveState
            let logBefore ← Core.getMessageLog
            Core.setMessageLog {}
            let aesopCand ← match preBranch? with
              | some (pre, _) => `(tactic| ($pre:tactic <;> aesop?))
              | none          => `(tactic| aesop?)
            try
              evalTactic aesopCand
              if (← getUnsolvedGoals).isEmpty then
                for msg in (← Core.getMessageLog).toArray do
                  let text ← msg.data.toString
                  if text.startsWith "Try this:" then
                    -- Strip `Try this:` and the trailing `[apply]` widget
                    -- annotation that Lean's `addSuggestion` interleaves
                    -- with the proof text.
                    let mut aesopProof := (text.drop 9).trim
                    if aesopProof.startsWith "[apply]" then
                      aesopProof := (aesopProof.drop 7).trim
                    capturedProof? := match preBranch? with
                      | some (_, preLabel) => some s!"{preLabel} <;> {aesopProof}"
                      | none               => some aesopProof
              else
                aesopSnapshot.restore
            catch _ => aesopSnapshot.restore
            Core.setMessageLog logBefore
            if capturedProof?.isNone then aesopSnapshot.restore
          Core.setMessageLog logBefore
          branchSnapshot.restore
          match capturedProof? with
          | none =>
            -- aesop didn't close this branch — abort inline-capture path.
            snapshot.restore
            return none
          | some proof =>
            -- The tag often has form `_uniqueId.caseName`; keep only the
            -- last component for readability.
            let caseName := tagName.componentsRev.head!.toString
            parts := parts.push s!"  | {caseName} => {proof}"
        snapshot.restore
        return some s!"induction {inductionVar.getId} with\n{String.intercalate "\n" parts.toList}"
      catch _ =>
        snapshot.restore
        return none

    -- `tryStrategy full compact ?inductionVar`:
    --   • Executes `full` (heavy closer with plain `aesop`) to actually close.
    --   • In suggest mode, if `inductionVar` is given, tries per-branch capture
    --     of aesop's proof to produce a single fully-inlined suggestion. If
    --     that fails (e.g. aesop can't close some branch), falls back to
    --     `compact` as the suggestion.
    let tryStrategy (full compact : TSyntax `tactic)
        (inductionVar? : Option Ident := none)
        (preBranch? : Option (TSyntax `tactic × String) := none) :
        TacticM Bool := do
      try
        -- First, in suggest mode, attempt per-branch capture for inlined
        -- suggestion. Done BEFORE the real `evalTactic` so we work on the
        -- original goal state. The capture function rolls back its state
        -- on completion, so it has no effect on what runs next.
        let inlinedSuggestion? ← match inductionVar?, suggest with
          | some v, true => captureInductionProof v preBranch?
          | _,      _    => pure none
        evalTactic (← `(tactic| solve | $full:tactic))
        if suggest then
          match inlinedSuggestion? with
          | some inlined =>
            let s : Lean.Meta.Tactic.TryThis.Suggestion := { suggestion := .string inlined }
            Lean.Meta.Tactic.TryThis.addSuggestion outerRef s
          | none =>
            Lean.Meta.Tactic.TryThis.addSuggestion outerRef compact
        return true
      catch _ =>
        return false

    -- ===== Step 4: try strategies in order =====

    -- Strategy 4a: maybe the closer alone closes the goal — no induction
    -- needed. Common for simp-only proofs like `f x = g x`.
    if (← tryStrategy closeBranch suggestionCloser) then return

    -- No inductive candidates? Nothing more to try.
    if allInductiveVars.isEmpty then return

    -- Strategy 4b: plain induction on each var, in order (predicates first).
    for inductionVar in allInductiveVars do
      let full    ← `(tactic| induction $inductionVar:term <;> $closeBranch:tactic)
      let compact ← `(tactic| induction $inductionVar:term <;> $suggestionCloser:tactic)
      if (← tryStrategy full compact (some inductionVar)) then return

    -- Strategy 4c: induct, then `intro h; cases h` on each resulting branch.
    -- Handles both "rule induction + invert the new hypothesis" (e.g.
    -- `Even n → ¬ Even (n+1)`) and "structural induction with an implication
    -- goal" (e.g. `IsFull t → IsFull (mirror t)`). Skipped when the
    -- induction subject's inductive type has many constructors — the inner
    -- `cases h` may also split on a many-ctor type, and the branch count
    -- explodes.
    let ctorCountOf (varIdent : Ident) : Nat :=
      match localCtx.findFromUserName? varIdent.getId with
      | none      => 999
      | some decl =>
        if let .const headName _ := decl.type.getAppFn then
          match environment.find? headName with
          | some (.inductInfo info) => info.ctors.length
          | _                       => 999
        else 999
    for inductionVar in allInductiveVars do
      if ctorCountOf inductionVar > 3 then continue
      let full ← `(tactic|
        induction $inductionVar:term <;> intro h <;> cases h <;> $closeBranch:tactic)
      let compact ← `(tactic|
        induction $inductionVar:term <;> intro h <;> cases h <;> $suggestionCloser:tactic)
      let preBranch ← `(tactic| (intro h <;> cases h))
      if (← tryStrategy full compact (some inductionVar)
          (preBranch? := some (preBranch, "intro h <;> cases h"))) then return

    -- Strategy 4c': rule induction on a predicate hypothesis, generalising
    -- over one data var at a time. Needed when the predicate's IH needs
    -- to range over a related parameter — e.g. for
    --   `(hm : m = 2*n+1) (h : Even m) ⊢ ¬ Even m`,
    -- inducting on `h` while generalising `n` (but NOT `m`, since `m` is
    -- the predicate's own index) gives a usable IH.
    for predicateVar in predicateHyps do
      for dataVar in dataVarIds do
        let full ← `(tactic|
          induction $predicateVar:term generalizing $dataVar:ident
          <;> $closeBranch:tactic)
        let compact ← `(tactic|
          induction $predicateVar:term generalizing $dataVar:ident
          <;> $suggestionCloser:tactic)
        if (← tryStrategy full compact) then return

    -- Strategy 4d: `induction v generalizing <other same-typed vars>`.
    -- Needed for accumulator-style proofs like
    --   `reverseAccu as xs = reverse xs ++ as`,
    -- where the IH must be quantified over the accumulator.
    for (firstVar, firstTypeHead) in dataVars do
      let otherSameTyped := dataVars.filterMap fun (varIdent, typeHead) =>
        if varIdent.getId != firstVar.getId && typeHead == firstTypeHead then
          some varIdent
        else
          none
      if otherSameTyped.isEmpty then continue
      let full ← `(tactic|
        induction $firstVar:term generalizing $otherSameTyped:ident*
        <;> $closeBranch:tactic)
      let compact ← `(tactic|
        induction $firstVar:term generalizing $otherSameTyped:ident*
        <;> $suggestionCloser:tactic)
      if (← tryStrategy full compact) then return

    -- Strategy 4e: mutual induction on a same-typed pair. `induction v
    -- generalizing w` gives an outer IH quantified over `w`; then a nested
    -- `induction w` produces the 4-case grid (nil/nil, nil/cons, …) typical
    -- of `f xs ys = g ys xs` style proofs.
    for (firstVar, firstTypeHead) in dataVars do
      for (secondVar, secondTypeHead) in dataVars do
        if firstVar.getId == secondVar.getId then continue
        if firstTypeHead != secondTypeHead then continue
        let full ← `(tactic|
          induction $firstVar:term generalizing $secondVar:ident
          <;> induction $secondVar:term
          <;> $closeBranch:tactic)
        let compact ← `(tactic|
          induction $firstVar:term generalizing $secondVar:ident
          <;> induction $secondVar:term
          <;> $suggestionCloser:tactic)
        if (← tryStrategy full compact) then return

    -- ===== Step 5: best-effort fallback =====
    -- No strategy fully closed the goal. As a final move, induct on the
    -- first candidate variable and try the closer per branch — leaves
    -- whichever subgoals couldn't be closed, so the user can inspect and
    -- continue manually. Wrapped in `try` because the induction itself
    -- may fail (e.g. on indexed predicate hypotheses where the index isn't
    -- a free variable); we'd rather leave a clean `unsolved goals` error
    -- than crash with `Invalid target`.
    try
      let fallback ← `(tactic|
        induction $(allInductiveVars[0]!):term <;> (try $closeBranch:tactic))
      evalTactic fallback
      if suggest then
        let compact ← `(tactic|
          induction $(allInductiveVars[0]!):term <;> (try $suggestionCloser:tactic))
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) compact
    catch _ => pure ()

elab_rules : tactic
  | `(tactic| inductosolve)            => runInductosolve false #[]
  | `(tactic| inductosolve [$ids,*])   => runInductosolve false ids.getElems
  | `(tactic| inductosolve?)           => runInductosolve true  #[]
  | `(tactic| inductosolve? [$ids,*])  => runInductosolve true  ids.getElems

end LoVe
