/-
# Inductosolve

A tactic that tries to solve induction proof goals automatically.

Usage:
  `inductosolve`              — black-box: silently closes the goal
  `inductosolve?`             — white-box: emits a suggestion w/ the working proof
  `inductosolve [foo, bar]`   — pass hint lemmas (works with `?` too)
-/

import Lean
import Aesop
import Mathlib.Tactic.Linarith
import Lean.Meta.Tactic.TryThis

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

namespace LoVe

private partial def resultIsProp : Expr → Bool
  | .forallE _ _ body _ => resultIsProp body
  | result              => result.isProp

private partial def stripForalls : Expr → Expr
  | .forallE _ _ body _ => stripForalls body
  | conclusion          => conclusion

syntax (name := inductosolve)         "inductosolve"  (" [" ident,* "]")? : tactic
syntax (name := inductosolveSuggest)  "inductosolve?" (" [" ident,* "]")? : tactic

private def runInductosolve (suggest : Bool) (hintLemmas : Array Ident) :
    TacticM Unit :=
  withMainContext do
    let localCtx    ← Lean.MonadLCtx.getLCtx
    let environment ← getEnv

    let aesopTac ←
      if hintLemmas.isEmpty then
        `(tactic| aesop)
      else
        `(tactic| aesop (add $[safe apply $hintLemmas:ident],*))
    let aesopSimpTac ←
      if hintLemmas.isEmpty then
        `(tactic| aesop)
      else
        `(tactic| aesop (add $[simp $hintLemmas:ident],*))
    let closeBranch ←
      if hintLemmas.isEmpty then
        `(tactic| (first
          -- Trivial closers
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
          | (simp_all [$[$hintLemmas:term],*]; done)
          | (simp     [$[$hintLemmas:term],*]; done)
          | (simp_all [$[$hintLemmas:term],*]; ac_rfl)
          | (simp     [$[$hintLemmas:term],*]; ac_rfl)
          | (simp_all [$[$hintLemmas:term],*]; linarith)
          | (simp     [$[$hintLemmas:term],*]; linarith)
          | (simp_all [$[$hintLemmas:term],*]; assumption)
          | (intros; simp_all [$[$hintLemmas:term],*]; done)
          | ((try simp only [$[$hintLemmas:term],*]); $aesopTac:tactic)
          | $aesopTac:tactic
          | $aesopSimpTac:tactic))

    let (predicateHyps, dataVars, generalizeCands) ← localCtx.foldlM
      (init := ((#[] : Array Ident),
                (#[] : Array (Ident × Name)),
                (#[] : Array Ident)))
      fun (predicateHyps, dataVars, generalizeCands) decl => do
        let typeHead := decl.type.getAppFn
        let varIdent := mkIdent decl.userName
        if let .const headName _ := typeHead then
          if let some (.inductInfo inductiveInfo) := environment.find? headName then
            if resultIsProp inductiveInfo.type then
              return (predicateHyps.push varIdent, dataVars, generalizeCands)
            else
              return (predicateHyps, dataVars.push (varIdent, headName),
                      generalizeCands.push varIdent)
        return (predicateHyps, dataVars, generalizeCands.push varIdent)
    let dataVarIds        := dataVars.map Prod.fst
    let allInductiveVars  := predicateHyps ++ dataVarIds

    let goalType ← instantiateMVars (← getMainTarget)
    let collectPredicateHead : Expr → NameSet → NameSet := fun expr acc =>
      if let .const headName _ := expr.getAppFn then
        match environment.find? headName with
        | some (.inductInfo info) =>
          if resultIsProp info.type then acc.insert headName else acc
        | _ => acc
      else acc
    let goalPredicateNames := collectPredicateHead (stripForalls goalType) {}

    let totalCtors : Nat := Id.run do
      let mut total := 0
      for predName in goalPredicateNames do
        if let some (.inductInfo info) := environment.find? predName then
          total := total + info.ctors.length
      pure total
    let useCtorAlts := totalCtors ≤ 4

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

    -- Applies two layers of constructors
    let closeBranchDepth1 ← wrapWithConstructorAlts closeBranch
    let closeBranch       ← wrapWithConstructorAlts closeBranchDepth1

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

    let outerRef ← getRef
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
                if !hintLemmas.isEmpty then
                  let cand ←
                    `(tactic| ((try simp_all [$[$hintLemmas:term],*]);
                               apply $ctorIdent <;> (first | rfl | assumption | aesop)))
                  candidates := candidates.push
                    (cand, s!"simp_all{simpHints}; apply {ctor} <;> assumption")
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
            snapshot.restore
            return none
          | some proof =>
            let caseName := tagName.componentsRev.head!.toString
            parts := parts.push s!"  | {caseName} => {proof}"
        snapshot.restore
        return some s!"induction {inductionVar.getId} with\n{String.intercalate "\n" parts.toList}"
      catch _ =>
        snapshot.restore
        return none

    let tryStrategy (full compact : TSyntax `tactic)
        (inductionVar? : Option Ident := none)
        (preBranch? : Option (TSyntax `tactic × String) := none) :
        TacticM Bool := do
      try
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

    if (← tryStrategy closeBranch suggestionCloser) then return

    if allInductiveVars.isEmpty then return

    for inductionVar in allInductiveVars do
      let full    ← `(tactic| induction $inductionVar:term <;> $closeBranch:tactic)
      let compact ← `(tactic| induction $inductionVar:term <;> $suggestionCloser:tactic)
      if (← tryStrategy full compact (some inductionVar)) then return

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

    for predicateVar in predicateHyps do
      for dataVar in generalizeCands do
        let full ← `(tactic|
          induction $predicateVar:term generalizing $dataVar:ident
          <;> $closeBranch:tactic)
        let compact ← `(tactic|
          induction $predicateVar:term generalizing $dataVar:ident
          <;> $suggestionCloser:tactic)
        if (← tryStrategy full compact) then return

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
