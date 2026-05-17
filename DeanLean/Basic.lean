import Lean
import DeanLean.Attr

/-- When true, ProvenTheorem emits axioms instead of looking up proofs.
    Headers don't need to import Proofs/ files → no cascade on proof changes.
    Set via: `set_option levelized.fast true` or Lake `-Klevelized.fast=true` -/
register_option levelized.fast : Bool := {
  defValue := false
  descr := "Fast mode: ProvenTheorem emits axioms, skipping proof lookup"
}

-- ════════════════════════════════════════════════════════════
-- § Test results environment extension
-- ════════════════════════════════════════════════════════════

/-- Per-conjecture test results: (passed, total) -/
structure TestResults where
  passed : Nat
  total : Nat
  deriving Inhabited

open Lean in
initialize testResultsExt : SimplePersistentEnvExtension (Name × TestResults) (Std.HashMap Name TestResults) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, r) =>
      let prev := (m[n]?).getD { passed := 0, total := 0 }
      m.insert n { passed := prev.passed + r.passed, total := prev.total + r.total }
    addImportedFn := fun arrays => Id.run do
      let mut m : Std.HashMap Name TestResults := {}
      for a in arrays do
        for (n, r) in a do
          let prev := (m[n]?).getD { passed := 0, total := 0 }
          m := m.insert n { passed := prev.passed + r.passed, total := prev.total + r.total }
      return m
  }

open Lean in
def getTestResults (env : Environment) (n : Name) : Option TestResults :=
  let m := testResultsExt.getState env
  m[n]?

-- ════════════════════════════════════════════════════════════
-- § Test macro: try/catch elaboration, always emits def
-- ════════════════════════════════════════════════════════════

open Lean Elab Command in
elab "Test " n:ident " := " body:term : command => do
  let name := n.getId
  let ns ← getCurrNamespace
  let fullName := ns ++ name
  -- Get the count for unique def naming
  let env ← getEnv
  let prev := getTestResults env fullName |>.getD { passed := 0, total := 0 }
  let idx := prev.total + 1
  let defName := Lean.mkIdent (name.appendAfter s!"_test_{idx}")
  -- Save state, attempt elaboration, check for new errors
  let savedState ← get
  let errorCountBefore := savedState.messages.toList.filter (·.severity == .error) |>.length
  try
    elabCommand (← `(noncomputable def $defName := $body))
  catch _ =>
    pure ()
  let stateAfter ← get
  let errorCountAfter := stateAfter.messages.toList.filter (·.severity == .error) |>.length
  if errorCountAfter == errorCountBefore then
    -- Passed: no new errors
    modifyEnv fun env => testResultsExt.addEntry env (fullName, { passed := 1, total := 1 })
  else
    -- Failed: restore state and emit sorry def
    set savedState
    elabCommand (← `(noncomputable def $defName : True := sorry))
    modifyEnv fun env => testResultsExt.addEntry env (fullName, { passed := 0, total := 1 })
    logWarning m!"Test {name} [{idx}]: ✗ failing"

open Lean in
macro "Wrap " n:ident " := " e:term : command => do
  `(noncomputable def $n := $e)

-- ════════════════════════════════════════════════════════════
-- § Manual test result registration
-- ════════════════════════════════════════════════════════════

/-!
For tests that can't be run as pure Lean expressions (e.g.,
conformance harnesses that read external files like spec.json,
network-bound checks, etc.), the user can manually register the
result counts produced by an out-of-band test run.

```
registerTestResults passes_atx_headings 13 18
TestedConjecture passes_atx_headings : ...     -- if 13/13 (all pass)
FailingConjecture passes_atx_headings : ...    -- if 13/18 (some fail)
```

The user is asserting the count is accurate. Re-run the harness
and update the numbers when code changes.

This is a stopgap until we have proper IO-during-elaboration
support, OR until we have a build script that writes results
to a Lean data file the manifest can import.
-/

open Lean Elab Command in
elab "registerTestResults " n:ident " passed " p:num " total " t:num : command => do
  let name := n.getId
  let ns ← getCurrNamespace
  let fullName := ns ++ name
  let passed := p.getNat
  let total := t.getNat
  if passed > total then
    throwError s!"registerTestResults {name}: passed ({passed}) > total ({total})"
  modifyEnv fun env => testResultsExt.addEntry env (fullName,
    { passed, total })

-- ════════════════════════════════════════════════════════════
-- § Helper: attach optional docstring to a theorem
-- ════════════════════════════════════════════════════════════

/-- If `doc?` is `some`, attach it as the docstring of `name` (in the
    current namespace). Used by the conjecture-style macros below so
    that doc-comments between successive declarations don't get gobbled
    by the term parser. -/
private def attachOptDoc (doc? : Option (Lean.TSyntax `Lean.Parser.Command.docComment))
    (name : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  if let some doc := doc? then
    let ns ← Lean.getCurrNamespace
    let fullName := ns ++ name
    let docText ← Lean.getDocStringText doc
    Lean.addDocString fullName docText

open Lean Elab Command in
elab "Signature " n:ident " : " t:term : command => do
  let name := n.getId
  let env ← getEnv
  let ns ← getCurrNamespace
  let fullName := ns ++ name
  match env.find? fullName |>.orElse fun _ => env.find? name with
  | some (.defnInfo val) =>
    if val.safety != .safe then
      throwError s!"{name} is partial/unsafe — use PartialSignature instead"
    elabCommand (← `(section variable (_sig_check : $t := $(n)) end))
  | some (.opaqueInfo _) =>
    throwError s!"{name} is partial — use PartialSignature instead"
  | some _ =>
    -- Exists but not a def — could be an axiom from fast mode or previous Signature
    elabCommand (← `(section variable (_sig_check : $t := $(n)) end))
  | none =>
    -- Doesn't exist yet — create as axiom (spec before implementation)
    logInfo m!"Signature {name}: not yet implemented, creating specification"
    elabCommand (← `(axiom $n : $t))

open Lean Elab Command in
elab "PartialSignature " n:ident " : " t:term : command => do
  let name := n.getId
  let env ← getEnv
  match env.find? name with
  | some (.defnInfo val) =>
    if val.safety == .safe then
      throwError s!"{name} is total — use Signature instead"
  | some (.opaqueInfo _) => pure ()
  | some _ => throwError s!"{name} is not a function definition"
  | none   => throwError s!"{name} not found in environment"
  elabCommand (← `(section variable (_sig_check : $t := $(n)) end))

open Lean Elab Command in
elab doc?:(docComment)? "ProvenTheorem " n:ident " : " t:term : command => do
  let name := n.getId
  let ns ← getCurrNamespace
  let env ← getEnv
  let fullName := ns ++ name
  -- Search open namespaces for existing declarations
  let scopes := (← getOpenDecls).filterMap fun d => match d with
    | .simple ns _ => some ns
    | _ => none
  let findInEnv (n : Lean.Name) : Bool :=
    (env.find? (ns ++ n)).isSome || (env.find? n).isSome ||
    scopes.any fun s => (env.find? (s ++ n)).isSome
  -- If name already exists (in any reachable scope), just verify the type matches
  if findInEnv name then
    elabCommand (← `(
      set_option linter.unusedVariables false in
      noncomputable example : $t := $n))
    attachOptDoc doc? n.getId
    return
  let fast := levelized.fast.get (← getOptions)
  if fast then
    elabCommand (← `(@[manifest_entry] axiom $n : $t))
    attachOptDoc doc? n.getId
  else
    let proofName := name.appendAfter "_proof"
    let derivationName := name.appendAfter "_derivation"
    let proofName := name.appendAfter "_proof"
    let derivationName := name.appendAfter "_derivation"
    let hasProof := findInEnv proofName
    let hasDeriv := findInEnv derivationName
    if hasProof then
      let rid := Lean.mkIdent proofName
      elabCommand (← `(@[manifest_entry] theorem $n : $t := $rid))
      attachOptDoc doc? n.getId
      -- Transitive sorry check (3 levels deep)
      let env ← getEnv
      let fullName := ns ++ name
      if let some info := env.find? fullName then
        let hasSorry := info.getUsedConstantsAsSet.any fun c =>
          if c == ``sorryAx then true
          else match env.find? c with
            | some ci => ci.getUsedConstantsAsSet.any fun c2 =>
                if c2 == ``sorryAx then true
                else match env.find? c2 with
                  | some ci2 => ci2.getUsedConstantsAsSet.contains ``sorryAx
                  | none => false
            | none => false
        if hasSorry then
          throwError s!"ProvenTheorem {name}: proof uses sorry — use DerivedConjecture or TestedConjecture instead"
    else if hasDeriv then
      let rid := Lean.mkIdent derivationName
      elabCommand (← `(@[manifest_entry] theorem $n : $t := $rid))
      attachOptDoc doc? n.getId
      let env ← getEnv
      let fullName := ns ++ name
      if let some info := env.find? fullName then
        let hasSorry := info.getUsedConstantsAsSet.any fun c =>
          if c == ``sorryAx then true
          else match env.find? c with
            | some ci => ci.getUsedConstantsAsSet.any fun c2 =>
                if c2 == ``sorryAx then true
                else match env.find? c2 with
                  | some ci2 => ci2.getUsedConstantsAsSet.contains ``sorryAx
                  | none => false
            | none => false
        if hasSorry then
          throwError s!"ProvenTheorem {name}: derivation uses sorry — use DerivedConjecture instead"
    else
      throwError s!"ProvenTheorem {name}: neither '{proofName}' nor '{derivationName}' found"

-- Helper: check if name already exists, verify type if so (for redundant manifests)
open Lean Elab Command in
private def checkRedundant (n : Lean.TSyntax `ident) (t : Lean.TSyntax `term) :
    CommandElabM Bool := do
  let name := n.getId
  let ns ← getCurrNamespace
  let env ← getEnv
  let fullName := ns ++ name
  let scopes := (← getOpenDecls).filterMap fun d => match d with
    | .simple ns _ => some ns
    | _ => none
  let found := (env.find? fullName).isSome || (env.find? name).isSome ||
    scopes.any fun s => (env.find? (s ++ name)).isSome
  if found then
    elabCommand (← `(
      set_option linter.unusedVariables false in
      noncomputable example : $t := $n))
    return true
  return false

-- TestedConjecture: requires foo_test OR passing Test results. Warns if vacuous.
open Lean Elab Command in
elab doc?:(docComment)? "TestedConjecture " n:ident " : " t:term : command => do
  let name := n.getId
  let ns ← getCurrNamespace
  let fullName := ns ++ name
  -- If already exists (e.g., via Restate), just verify type matches
  if (← checkRedundant n t) then return
  -- Validate evidence level
  let env ← getEnv
  -- Search for test results in current namespace and open namespaces
  let scopes := (← getOpenDecls).filterMap fun d => match d with
    | .simple ns _ => some ns
    | _ => none
  let testResults := (getTestResults env fullName).orElse fun _ =>
    (getTestResults env name).orElse fun _ =>
    scopes.findSome? fun s => getTestResults env (s ++ name)
  match testResults with
  | some results =>
    if results.passed < results.total then
      throwError s!"TestedConjecture {name}: {results.total - results.passed}/{results.total} tests failing — use FailingConjecture instead"
    if results.passed == 0 then
      throwError s!"TestedConjecture {name}: no passing tests found"
    logInfo m!"TestedConjecture {name}: passing {results.passed}/{results.total} tests"
  | none =>
    -- Fall back to legacy foo_test lookup
    let testId := name.appendAfter "_test"
    let testName := Lean.mkIdent testId
    elabCommand (← `(
      set_option linter.unusedVariables false in
      noncomputable def _tc_check := $testName))
    -- Check for vacuous truth indicators
    let env ← getEnv
    let fullTestName := ns ++ testId
    let info? := env.find? fullTestName |>.orElse fun _ => env.find? testId
    match info? with
    | some info =>
      let usedConsts := info.getUsedConstantsAsSet
      let vacuousIndicators := #[``absurd, ``False.elim, ``Not.elim, ``False.rec]
      let hasVacuous := vacuousIndicators.any fun c => usedConsts.contains c
      if hasVacuous then
        let classicalName := testId.appendAfter "_is_classical"
        let fullClassical := ns ++ classicalName
        let isMarkedClassical := (env.find? fullClassical).isSome || (env.find? classicalName).isSome
        if !isMarkedClassical then
          logWarning m!"TestedConjecture {name}: ⚠ test witness may be vacuous (uses absurd/False.elim). Add `def {testId}_is_classical := ()` to suppress, or provide a positive test."
    | none => pure ()
  -- Create theorem
  elabCommand (← `(@[manifest_entry] theorem $n : $t := by sorry))
  attachOptDoc doc? n.getId

-- FailingConjecture: requires tests, at least one failing.
open Lean Elab Command in
elab doc?:(docComment)? "FailingConjecture " n:ident " : " t:term : command => do
  let name := n.getId
  let ns ← getCurrNamespace
  let fullName := ns ++ name
  -- ALWAYS validate evidence level, even if redundant
  let env ← getEnv
  match getTestResults env fullName with
  | some results =>
    if results.passed == results.total then
      logWarning m!"FailingConjecture {name}: all {results.total} tests pass — promote to TestedConjecture"
    else
      logInfo m!"FailingConjecture {name}: passing {results.passed}/{results.total} tests"
  | none =>
    throwError s!"FailingConjecture {name}: no tests found — use Test macro to define tests"
  -- Now handle redundancy or create theorem
  if (← checkRedundant n t) then return
  elabCommand (← `(@[manifest_entry] theorem $n : $t := by sorry))
  attachOptDoc doc? n.getId

/-- Check whether an Expr is `True` after unfolding all `forall` binders.
    True if the type is trivially inhabited (`True`, `∀ x, True`, etc.). -/
private def isVacuousProp : Lean.Expr → Bool
  | .const ``True _ => true
  | .forallE _ _ body _ => isVacuousProp body
  | _ => false

/-- Walk the environment, look for any existing theorem (not axiom, not
    sorry-using) whose type is definitionally equal to `t`. If found,
    or if the type is vacuous (`True` or `∀ ..., True`), emit a warning. -/
private def warnIfTypeAlreadyProven (n : Lean.TSyntax `ident) (t : Lean.TSyntax `term)
    (env : Lean.Environment) : Lean.Elab.Command.CommandElabM Unit := do
  let name := n.getId
  -- Elaborate t to an Expr in command context
  let liftResult ← Lean.Elab.Command.liftTermElabM do
    let tExpr ← Lean.Elab.Term.elabTerm t none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let tExpr ← Lean.instantiateMVars tExpr
    -- First check: is the type vacuous (just True, possibly under foralls)?
    if isVacuousProp tExpr then
      return #[`«» /- sentinel meaning "vacuous" -/]
    -- Otherwise walk the env; find any theorem with defeq type that doesn't use sorry
    let mut hits : Array Lean.Name := #[]
    for (existingName, info) in env.constants do
      if existingName == name then continue
      -- Skip non-theorems
      match info with
      | .thmInfo _ => pure ()
      | _ => continue
      -- Skip private/internal names and compiler-generated equation lemmas
      let s := existingName.toString
      if s.startsWith "_private." || s.startsWith "_aux." then continue
      -- Skip equation lemmas (e.g., `foo.eq_1`, `foo._unfold`, `foo.match_N`)
      if (s.splitOn ".eq_").length > 1 || (s.splitOn "._unfold").length > 1 ||
         (s.splitOn ".match_").length > 1 || (s.splitOn ".proof_").length > 1 then
        continue
      -- Skip sorry-using theorems (other UnprovenConjectures)
      if info.getUsedConstantsAsSet.contains ``sorryAx then continue
      -- Defeq check (try, ignore errors)
      try
        if ← Lean.Meta.isDefEq info.type tExpr then
          hits := hits.push existingName
          if hits.size ≥ 3 then break  -- bound the search
      catch _ => continue
    return hits
  if liftResult.size == 1 && liftResult[0]! == `«» then
    Lean.logWarning m!"UnprovenConjecture {name}: type is vacuous (reduces to `True`). \
      The actual claim is in the doc-comment. Consider:\n\
      • If the claim is testable at runtime: convert to a TestedConjecture with a smoke test\n\
      • If the claim is about source structure: use a CI grep check instead\n\
      • If the claim is about the OS: keep as UnprovenConjecture but document the falsifying observation"
  else if liftResult.size > 0 then
    let names := String.intercalate ", " (liftResult.toList.map toString)
    Lean.logWarning m!"UnprovenConjecture {name}: type is already proven by [{names}]. \
      Consider deleting this UnprovenConjecture and using the existing theorem(s) directly."

open Lean Elab Command in
elab doc?:(docComment)? "UnprovenConjecture " n:ident " : " t:term : command => do
  if (← checkRedundant n t) then return
  -- Detect duplicates: if some existing theorem has the same type and
  -- doesn't use sorry, warn that this UnprovenConjecture is redundant.
  let env ← getEnv
  warnIfTypeAlreadyProven n t env
  elabCommand (← `(@[manifest_entry] theorem $n : $t := by sorry))
  attachOptDoc doc? n.getId

-- ManifestAxiom: a permanent environmental assumption we explicitly accept.
-- Identical to UnprovenConjecture in proof terms (reduces to sorry), but
-- tagged as manifest_axiom to distinguish in trust reports.
-- ManifestAxiom in a trust report = fully attested (as proven as possible).
-- UnprovenConjecture in a trust report = partial (has TODOs to close).
open Lean Elab Command in
elab doc?:(docComment)? "ManifestAxiom " n:ident " : " t:term : command => do
  if (← checkRedundant n t) then return
  elabCommand (← `(@[manifest_entry] theorem $n : $t := by sorry))
  attachOptDoc doc? n.getId
  let ns ← getCurrNamespace
  let fullName := ns ++ n.getId
  modifyEnv fun env => manifestAxiomAttr.ext.addEntry env fullName

private def findSorryDeps (env : Lean.Environment) (info : Lean.ConstantInfo) : Array Lean.Name := Id.run do
  let consts := info.getUsedConstantsAsSet
  let mut result : Array Lean.Name := #[]
  for c in consts do
    if c == ``sorryAx then continue
    match env.find? c with
    | some cinfo =>
      if cinfo.getUsedConstantsAsSet.contains ``sorryAx then
        result := result.push c
    | none => pure ()
  return result

open Lean Elab Command in
elab doc?:(docComment)? "DerivedConjecture " n:ident " : " t:term : command => do
  if (← checkRedundant n t) then return
  let name := n.getId
  let ns ← getCurrNamespace
  let derivationId := name.appendAfter "_derivation"
  let derivationName := Lean.mkIdent derivationId
  elabCommand (← `(
    set_option linter.unusedVariables false in
    noncomputable def _dc_check := $derivationName))
  let env ← getEnv
  let fullName := ns ++ derivationId
  let info? := env.find? fullName |>.orElse fun _ => env.find? derivationId
  match info? with
  | none => logWarning m!"DerivedConjecture: could not find '{derivationId}' for dependency analysis"
  | some info =>
    let allDeps := info.getUsedConstantsAsSet
    let sorryDeps := findSorryDeps env info
    -- Count total non-builtin theorem deps vs sorry deps for fraction
    let mut totalTheorems : Nat := 0
    let mut provenTheorems : Nat := 0
    for c in allDeps do
      if c == ``sorryAx then continue
      match env.find? c with
      | some cinfo =>
        if let .thmInfo _ := cinfo then
          totalTheorems := totalTheorems + 1
          if !cinfo.getUsedConstantsAsSet.contains ``sorryAx then
            provenTheorems := provenTheorems + 1
      | none => pure ()
    if sorryDeps.isEmpty then
      logInfo m!"DerivedConjecture {name}: no sorry dependencies — consider promoting to ProvenTheorem"
    else
      let pct := if totalTheorems > 0 then provenTheorems * 100 / totalTheorems else 0
      -- Distinguish ManifestAxiom deps (permanent, OK) from UnprovenConjecture deps (TODOs)
      let manifestAxiomDeps := sorryDeps.filter (fun d => hasManifestAxiomAttr env d)
      let unconjDeps := sorryDeps.filter (fun d => !hasManifestAxiomAttr env d)
      if unconjDeps.isEmpty then
        logInfo m!"DerivedConjecture {name}: fully attested ({provenTheorems}/{totalTheorems} theorem deps proven, {pct}%)\n  manifest axioms (permanent): {manifestAxiomDeps}"
      else
        logInfo m!"DerivedConjecture {name}: partial ({provenTheorems}/{totalTheorems} theorem deps proven, {pct}%)\n  manifest axioms (permanent): {manifestAxiomDeps}\n  unproven conjectures (TODOs): {unconjDeps}"
    -- ENFORCEMENT: every sorry dep must be a manifest entry.
    let strays := sorryDeps.filter (fun d => !hasManifestEntryAttr env d)
    unless strays.isEmpty do
      throwError s!"DerivedConjecture {name}: sorry deps must be declared via manifest macros (UnprovenConjecture/TestedConjecture/DecomposedConjecture/DerivedConjecture/ProvenTheorem). These deps are stray sorries, not manifest entries:\n  {strays}\nFix by either wrapping each in the appropriate manifest macro, or replacing with a real proof."
  -- Blame analysis: if this conjecture has failing tests, report which deps are responsible
  let env ← getEnv
  let conjFullName := ns ++ name
  match getTestResults env conjFullName with
  | some results =>
    if results.passed < results.total then
      let mut blame : Array String := #[]
      let info? := (env.find? (ns ++ derivationId)) |>.orElse fun _ => env.find? derivationId
      if let some info := info? then
        let sorryDeps := findSorryDeps env info
        for dep in sorryDeps do
          match getTestResults env dep with
          | some depResults =>
            if depResults.passed < depResults.total then
              blame := blame.push s!"  {dep}: passing {depResults.passed}/{depResults.total} tests"
          | none => blame := blame.push s!"  {dep}: no tests"
      if blame.isEmpty then
        logWarning m!"DerivedConjecture {name}: passing {results.passed}/{results.total} tests — cannot localize blame"
      else
        logWarning m!"DerivedConjecture {name}: passing {results.passed}/{results.total} tests\n  blame:\n{"\n".intercalate blame.toList}"
  | none => pure ()
  elabCommand (← `(@[manifest_entry] theorem $n : $t := by sorry))
  attachOptDoc doc? n.getId

-- DecomposedConjecture: broken into pieces, ALL pieces must be at least tested.
-- Strictly stronger than TestedConjecture, weaker than DerivedConjecture.
-- The derivation is a real proof; the pieces are lemmas that may be sorry but must have _test.
open Lean Elab Command in
elab doc?:(docComment)? "DecomposedConjecture " n:ident " : " t:term : command => do
  if (← checkRedundant n t) then return
  let name := n.getId
  let ns ← getCurrNamespace
  let derivationId := name.appendAfter "_derivation"
  let derivationName := Lean.mkIdent derivationId
  elabCommand (← `(
    set_option linter.unusedVariables false in
    noncomputable def _decomp_check := $derivationName))
  let env ← getEnv
  let fullName := ns ++ derivationId
  let info? := env.find? fullName |>.orElse fun _ => env.find? derivationId
  match info? with
  | none => logWarning m!"DecomposedConjecture: could not find '{derivationId}'"
  | some info =>
    let sorryDeps := findSorryDeps env info
    let scopes := (← getOpenDecls).filterMap fun d => match d with
      | .simple ns _ => some ns
      | _ => none
    let findConst (n : Lean.Name) : Option Lean.ConstantInfo :=
      (env.find? (ns ++ n)) |>.orElse fun _ =>
      (env.find? n) |>.orElse fun _ =>
      scopes.findSome? fun s => env.find? (s ++ n)
    -- Check ALL sorry deps have _test witnesses or Test results
    let mut allTested := true
    let mut details : Array String := #[]
    for dep in sorryDeps do
      let hasTestResult := (getTestResults env dep).isSome
      let testName := dep.appendAfter "_test"
      let hasLegacyTest := (findConst testName).isSome
      if hasTestResult || hasLegacyTest then
        details := details.push s!"  {dep}: tested ◐"
      else
        allTested := false
        details := details.push s!"  {dep}: UNTESTED ✗ — needs {testName}"
    if !allTested then
      throwError s!"DecomposedConjecture {name}: all sorry deps must be at least TestedConjecture\n{"\n".intercalate details.toList}"
    if sorryDeps.isEmpty then
      logInfo m!"DecomposedConjecture {name}: no sorry deps — consider promoting to DerivedConjecture or ProvenTheorem"
    else
      logInfo m!"DecomposedConjecture {name}: all {sorryDeps.size} lemmas tested ◐\n{"\n".intercalate details.toList}"
    -- ENFORCEMENT: every sorry dep must be a manifest entry.
    let strays := sorryDeps.filter (fun d => !hasManifestEntryAttr env d)
    unless strays.isEmpty do
      throwError s!"DecomposedConjecture {name}: sorry deps must be declared via manifest macros (UnprovenConjecture/TestedConjecture/DecomposedConjecture/DerivedConjecture/ProvenTheorem). These deps are stray sorries, not manifest entries:\n  {strays}\nFix by either wrapping each in the appropriate manifest macro, or replacing with a real proof."
  -- Blame analysis: if this conjecture has failing tests, report which deps are responsible
  let env ← getEnv
  let conjFullName := ns ++ name
  match getTestResults env conjFullName with
  | some results =>
    if results.passed < results.total then
      let mut blame : Array String := #[]
      let info? := (env.find? (ns ++ derivationId)) |>.orElse fun _ => env.find? derivationId
      if let some info := info? then
        let sorryDeps := findSorryDeps env info
        for dep in sorryDeps do
          match getTestResults env dep with
          | some depResults =>
            if depResults.passed < depResults.total then
              blame := blame.push s!"  {dep}: passing {depResults.passed}/{depResults.total} tests"
          | none => blame := blame.push s!"  {dep}: no tests"
      if blame.isEmpty then
        logWarning m!"DecomposedConjecture {name}: passing {results.passed}/{results.total} tests — cannot localize blame"
      else
        logWarning m!"DecomposedConjecture {name}: passing {results.passed}/{results.total} tests\n  blame:\n{"\n".intercalate blame.toList}"
  | none => pure ()
  elabCommand (← `(@[manifest_entry] theorem $n : $t := by sorry))
  attachOptDoc doc? n.getId

macro "FastHeader " n:ident " : " t:term : command =>
  `(@[manifest_entry] axiom $n : $t)

-- VerifyAxiom: confirm a fast-mode axiom has a matching proof (CI-only)
open Lean Elab Command in
elab "VerifyAxiom " n:ident " : " t:term : command => do
  let name := n.getId
  let proofName := name.appendAfter "_proof"
  let derivationName := name.appendAfter "_derivation"
  let env ← getEnv
  let ns ← getCurrNamespace
  -- Search with namespace prefix, without, and with all open namespaces
  let scopes := (← getOpenDecls).filterMap fun d => match d with
    | .simple ns _ => some ns
    | _ => none
  let findName (suffix : Lean.Name) : Bool :=
    (env.find? (ns ++ suffix)).isSome || (env.find? suffix).isSome ||
    scopes.any fun s => (env.find? (s ++ suffix)).isSome
  let hasProof := findName proofName
  let hasDeriv := findName derivationName
  if hasProof then
    let rid := Lean.mkIdent proofName
    elabCommand (← `(
      set_option linter.unusedVariables false in
      noncomputable example : $t := $rid))
    logInfo m!"VerifyAxiom {name}: ✓ matched by {proofName}"
  else if hasDeriv then
    let rid := Lean.mkIdent derivationName
    elabCommand (← `(
      set_option linter.unusedVariables false in
      noncomputable example : $t := $rid))
    logInfo m!"VerifyAxiom {name}: ✓ matched by {derivationName}"
  else
    throwError s!"VerifyAxiom {name}: ✗ neither '{proofName}' nor '{derivationName}' found — AXIOM UNVERIFIED"

open Lean Elab Command in
elab "ExternalTheorem " n:ident " := " src:term " : " t:term : command => do
  elabCommand (← `(
    set_option linter.unusedVariables false in
    noncomputable def _ext_check : $t := $src))
  elabCommand (← `(noncomputable def $n : $t := $src))

-- ════════════════════════════════════════════════════════════
-- § RestateTheorem: forward a claim from another namespace
-- ════════════════════════════════════════════════════════════

-- Restate a claim from another namespace, preserving its evidence level.
-- Automatically dispatches to ProvenTheorem/DerivedConjecture/TestedConjecture
-- based on whether the source has sorry dependencies.
--
-- Two forms:
--   Restate foo from L3m.Manifests.Sandbox   -- explicit source namespace
--   Restate foo                              -- searches open namespaces
open Lean Elab Command in
private def restateImpl (n : Lean.TSyntax `ident) (sourceName : Lean.Name) : CommandElabM Unit := do
  let name := n.getId
  let env ← getEnv
  match env.find? sourceName with
  | none => throwError s!"Restate: '{sourceName}' not found in environment"
  | some info =>
    let localNs ← getCurrNamespace
    let localName := localNs ++ name
    if (env.find? localName).isSome then return
    let hasSorry := info.getUsedConstantsAsSet.contains ``sorryAx
    let srcIdent := Lean.mkIdent sourceName
    elabCommand (← `(@[manifest_entry] noncomputable def $n := $srcIdent))
    if !hasSorry then
      logInfo m!"Restate {name}: ● ProvenTheorem (from {sourceName})"
    else
      let derivationName := sourceName.appendAfter "_derivation"
      let hasDeriv := (env.find? derivationName).isSome
      let hasTests := (getTestResults env sourceName).isSome
      if hasDeriv then
        logInfo m!"Restate {name}: ◕ DerivedConjecture (from {sourceName})"
      else if hasTests then
        let results := (getTestResults env sourceName).get!
        logInfo m!"Restate {name}: ◐ TestedConjecture, {results.passed}/{results.total} tests (from {sourceName})"
      else if hasManifestAxiomAttr env sourceName then
        logInfo m!"Restate {name}: ◆ ManifestAxiom (from {sourceName})"
      else
        logInfo m!"Restate {name}: ○ UnprovenConjecture (from {sourceName})"

-- Explicit form: Restate foo from Namespace
open Lean Elab Command in
elab "Restate " n:ident " from " ns:ident : command => do
  let sourceName := ns.getId ++ n.getId
  restateImpl n sourceName

-- Implicit form: Restate foo (searches current namespace, root, open scopes)
open Lean Elab Command in
elab "Restate " n:ident : command => do
  let name := n.getId
  let env ← getEnv
  let ns ← getCurrNamespace
  let scopes := (← getOpenDecls).filterMap fun d => match d with
    | .simple ns _ => some ns
    | _ => none
  let sourceName ←
    if (env.find? name).isSome then pure name
    else if (env.find? (ns ++ name)).isSome then pure (ns ++ name)
    else
      match scopes.findSome? fun s => if (env.find? (s ++ name)).isSome then some (s ++ name) else none with
      | some found => pure found
      | none => throwError s!"Restate: '{name}' not found in current namespace, root, or any open namespace"
  restateImpl n sourceName

-- Legacy aliases
macro "RestateTheorem " n:ident " from " ns:ident : command =>
  `(Restate $n from $ns)

macro "RestateConjecture " n:ident " from " ns:ident : command =>
  `(Restate $n from $ns)


-- ════════════════════════════════════════════════════════════
-- § Call graph analysis: prove what IO is reachable from a root
-- ════════════════════════════════════════════════════════════

-- Transitively collect all constants reachable from a root constant.
-- Used to verify "only these IO operations are reachable from main."
open Lean in
private partial def reachableFrom (env : Environment) (root : Name) : NameSet :=
  go (NameSet.empty) root
where
  go (visited : NameSet) (n : Name) : NameSet :=
    if visited.contains n then visited
    else
      let visited := visited.insert n
      match env.find? n with
      | none => visited
      | some info => info.getUsedConstantsAsSet.fold go visited

-- Check that all IO-bearing constants reachable from `root` are in `allowed`.
-- If the list is complete, emits `theorem <root>_io_surface_complete : True`
-- as a proof artifact. If the list is INCOMPLETE, throws an error naming
-- the unexpected constants — the build FAILS until the list is fixed.
--
-- Usage:
--   PureExcept main allows L3m.Runtime.callLlm IO.Process.output IO.FS.readFile
open Lean Elab Command in
elab "PureExcept " root:ident " allows " allowed:ident* : command => do
  let rootName := root.getId
  let allowedSet : NameSet := allowed.foldl (init := .empty) fun s id => s.insert id.getId
  let env ← getEnv
  match env.find? rootName with
  | none => throwError s!"PureExcept: root '{rootName}' not found"
  | some _ =>
    let reachable := reachableFrom env rootName
    let mut ioLeaks : Array Name := #[]
    for c in reachable do
      if allowedSet.contains c then continue
      -- Skip private-name mangled constants (they contain numeric components)
      if c.toString.startsWith "_private." then continue
      match env.find? c with
      | none => continue
      | some info =>
        let typeStr := toString info.type
        if (typeStr.splitOn "IO ").length > 1 || (typeStr.splitOn "EIO ").length > 1 ||
           (typeStr.splitOn "BaseIO").length > 1 then
          ioLeaks := ioLeaks.push c
    if ioLeaks.isEmpty then
      -- Emit a theorem as proof artifact: <root>_io_surface_complete
      let thmName := Lean.mkIdent (rootName.appendAfter "_io_surface_complete")
      elabCommand (← `(@[manifest_entry] theorem $thmName : True := trivial))
      logInfo m!"PureExcept {rootName}: ✓ complete ({reachable.size} reachable, all pure or in allow-list)"
    else
      throwError s!"PureExcept {rootName}: {ioLeaks.size} unexpected IO constants reachable. Add to the allow-list:\n  {ioLeaks.toList}"

-- ════════════════════════════════════════════════════════════
-- § AxiomsAllowed: verify the complete axiom surface
-- ════════════════════════════════════════════════════════════

-- Check that all axiom constants reachable from `root` are in `allowed`.
-- This catches any new axiom (Unproven/Tested/Derived Conjectures, raw `axiom`
-- declarations, or any other sorry-bearing constant) that sneaks into the
-- codebase without explicit approval.
--
-- Usage:
--   AxiomsAllowed L3m.Runtime.runLoop allows single_writer io_read_after_write ...
--
-- If it compiles: the axiom list is complete.
-- If it fails: build breaks with the name of the unexpected axiom.
open Lean Elab Command in
elab "AxiomsAllowed " root:ident " allows " allowed:ident* : command => do
  let rootName := root.getId
  let allowedSet : NameSet := allowed.foldl (init := .empty) fun s id => s.insert id.getId
  let env ← getEnv
  match env.find? rootName with
  | none => throwError s!"AxiomsAllowed: root '{rootName}' not found"
  | some _ =>
    let reachable := reachableFrom env rootName
    let mut axioms : Array Name := #[]
    -- Include the root itself if it's a manifest-entry axiom
    if let some rootInfo := env.find? rootName then
      match rootInfo with
      | .axiomInfo _ =>
        if !allowedSet.contains rootName then
          if rootName != ``Classical.choice && rootName != ``propext && rootName != ``Quot.sound then
            axioms := axioms.push rootName
      | _ =>
        if rootInfo.getUsedConstantsAsSet.contains ``sorryAx && hasManifestEntryAttr env rootName then
          if !allowedSet.contains rootName then
            axioms := axioms.push rootName
    for c in reachable do
      if c == rootName then continue  -- already handled above
      if c == ``sorryAx then continue
      if allowedSet.contains c then continue
      if c.toString.startsWith "_private." then continue
      match env.find? c with
      | none => continue
      | some (.axiomInfo _) =>
        -- Skip standard Lean axioms that everyone uses
        if c == ``Classical.choice || c == ``propext || c == ``Quot.sound then continue
        axioms := axioms.push c
      | some info =>
        -- Also catch theorems that transitively use sorryAx
        if info.getUsedConstantsAsSet.contains ``sorryAx then
          -- But only flag the ones marked @[manifest_entry] (our conjectures)
          if hasManifestEntryAttr env c then
            axioms := axioms.push c
    if axioms.isEmpty then
      let thmName := Lean.mkIdent (rootName.appendAfter "_axioms_complete")
      elabCommand (← `(@[manifest_entry] theorem $thmName : True := trivial))
      logInfo m!"AxiomsAllowed {rootName}: ✓ complete (no unexpected axioms in {reachable.size} reachable constants)"
    else
      throwError s!"AxiomsAllowed {rootName}: {axioms.size} unexpected axioms reachable. Add to the allow-list:\n  {axioms.toList}"



-- ════════════════════════════════════════════════════════════
-- § FullyAttested: verify all sorry deps are ManifestAxioms
-- ════════════════════════════════════════════════════════════

-- Check that every sorry-bearing dependency of `root` is tagged @[manifest_axiom].
-- If so, the derivation is "fully attested" — as proven as it can be.
-- If any dep is an UnprovenConjecture (manifest_entry but NOT manifest_axiom),
-- the build fails naming the TODOs.
--
-- Usage:
--   FullyAttested l3m_is_sandboxed
open Lean Elab Command in
elab "FullyAttested " root:ident : command => do
  let rootName := root.getId
  let env ← getEnv
  let ns ← getCurrNamespace
  let fullName := ns ++ rootName
  let resolvedName := if (env.find? fullName).isSome then fullName else rootName
  match env.find? resolvedName with
  | none => throwError s!"FullyAttested: '{rootName}' not found"
  | some _ =>
    let reachable := reachableFrom env resolvedName
    let mut todos : Array Name := #[]
    for c in reachable do
      if c == resolvedName then continue  -- skip the root itself
      if c == ``sorryAx then continue
      if c.toString.startsWith "_private." then continue
      match env.find? c with
      | none => continue
      | some info =>
        if info.getUsedConstantsAsSet.contains ``sorryAx then
          if hasManifestEntryAttr env c then
            if !hasManifestAxiomAttr env c then
              todos := todos.push c
    if todos.isEmpty then
      let thmName := Lean.mkIdent (rootName.appendAfter "_fully_attested")
      elabCommand (← `(@[manifest_entry] theorem $thmName : True := trivial))
      logInfo m!"FullyAttested {rootName}: ✓ all sorry deps are ManifestAxioms — theorem is as proven as possible"
    else
      throwError s!"FullyAttested {rootName}: {todos.size} UnprovenConjecture deps (TODOs) remain:\n  {todos.toList}\nConvert these to ManifestAxiom if they are permanent assumptions, or prove them."
