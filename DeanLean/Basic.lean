import Lean

/-- When true, ProvenTheorem emits axioms instead of looking up proofs.
    Headers don't need to import Proofs/ files → no cascade on proof changes.
    Set via: `set_option levelized.fast true` or Lake `-Klevelized.fast=true` -/
register_option levelized.fast : Bool := {
  defValue := false
  descr := "Fast mode: ProvenTheorem emits axioms, skipping proof lookup"
}

open Lean in
macro "Wrap " n:ident " := " e:term : command => do
  `(noncomputable def $n := $e)

open Lean Elab Command in
elab "Signature " n:ident " : " t:term : command => do
  let name := n.getId
  let env ← getEnv
  match env.find? name with
  | some (.defnInfo val) =>
    if val.safety != .safe then
      throwError s!"{name} is partial/unsafe — use PartialSignature instead"
  | some (.opaqueInfo _) =>
    throwError s!"{name} is partial — use PartialSignature instead"
  | some _ => throwError s!"{name} is not a function definition"
  | none   => throwError s!"{name} not found in environment"
  elabCommand (← `(section variable (_sig_check : $t := $(n)) end))

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
elab "ProvenTheorem " n:ident " : " t:term : command => do
  let fast := levelized.fast.get (← getOptions)
  if fast then
    -- Fast mode: axiom only. Header doesn't import Proofs.
    -- Verification happens in Verify/ files (CI-only).
    elabCommand (← `(axiom $n : $t))
  else
    -- Full mode: look up _proof or _derivation.
    -- Header must import Proofs for this to work.
    let name := n.getId
    let proofName := name.appendAfter "_proof"
    let derivationName := name.appendAfter "_derivation"
    let env ← getEnv
    let ns ← getCurrNamespace
    let hasProof := (env.find? (ns ++ proofName)).isSome || (env.find? proofName).isSome
    let hasDeriv := (env.find? (ns ++ derivationName)).isSome || (env.find? derivationName).isSome
    if hasProof then
      let rid := Lean.mkIdent proofName
      elabCommand (← `(theorem $n : $t := $rid))
    else if hasDeriv then
      let rid := Lean.mkIdent derivationName
      elabCommand (← `(theorem $n : $t := $rid))
    else
      throwError s!"ProvenTheorem {name}: neither '{proofName}' nor '{derivationName}' found"

open Lean in
macro "TestedConjecture " n:ident " : " t:term : command => do
  let testName := Lean.mkIdent (n.getId.appendAfter "_test")
  `(set_option linter.unusedVariables false in
    noncomputable def _tc_check := $testName
    theorem $n : $t := by sorry)

macro "UnprovenConjecture " n:ident " : " t:term : command =>
  `(theorem $n : $t := by sorry)

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
elab "DerivedConjecture " n:ident " : " t:term : command => do
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
      logInfo m!"DerivedConjecture {name}: {provenTheorems}/{totalTheorems} theorem deps proven ({pct}%)\n  sorry deps: {sorryDeps}"
  elabCommand (← `(theorem $n : $t := by sorry))

-- FractionalTheorem: explicit decomposition with proof coverage tracking
-- Shows which lemmas are proven vs tested vs unproven
open Lean Elab Command in
elab "FractionalTheorem " n:ident " : " t:term " from " deps:ident,+ : command => do
  let name := n.getId
  let ns ← getCurrNamespace
  let derivationId := name.appendAfter "_derivation"
  let derivationName := Lean.mkIdent derivationId
  -- Check derivation exists
  elabCommand (← `(
    set_option linter.unusedVariables false in
    noncomputable def _ft_check := $derivationName))
  -- Analyze each dependency
  let env ← getEnv
  let scopes := (← getOpenDecls).filterMap fun d => match d with
    | .simple ns _ => some ns
    | _ => none
  let findConst (name : Lean.Name) : Option Lean.ConstantInfo :=
    (env.find? (ns ++ name)) |>.orElse fun _ =>
    (env.find? name) |>.orElse fun _ =>
    scopes.findSome? fun s => env.find? (s ++ name)
  let mut proven := 0
  let mut tested := 0
  let mut unproven := 0
  let mut details : Array String := #[]
  for dep in deps.getElems do
    let depName := dep.getId
    match findConst depName with
    | some info =>
      if info.getUsedConstantsAsSet.contains ``sorryAx then
        -- Has sorry — is it tested or unproven?
        let testName := depName.appendAfter "_test"
        if (findConst testName).isSome then
          tested := tested + 1
          details := details.push s!"  {depName}: tested ◐"
        else
          unproven := unproven + 1
          details := details.push s!"  {depName}: unproven ○"
      else
        proven := proven + 1
        details := details.push s!"  {depName}: proven ●"
    | none =>
      unproven := unproven + 1
      details := details.push s!"  {depName}: NOT FOUND ✗"
  let total := proven + tested + unproven
  let pct := if total > 0 then proven * 100 / total else 0
  logInfo m!"FractionalTheorem {name}: {proven}/{total} proven ({pct}%)\n{"\n".intercalate details.toList}"
  if proven == total then
    logInfo m!"  → All lemmas proven! Consider promoting to ProvenTheorem."
  elabCommand (← `(theorem $n : $t := by sorry))

macro "FastHeader " n:ident " : " t:term : command =>
  `(axiom $n : $t)

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
