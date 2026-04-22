import Lean

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
    let sorryDeps := findSorryDeps env info
    if sorryDeps.isEmpty then
      logInfo m!"DerivedConjecture {name}: no sorry dependencies — consider promoting to ProvenTheorem"
    else
      logInfo m!"DerivedConjecture {name} depends on: {sorryDeps}"
  elabCommand (← `(theorem $n : $t := by sorry))

macro "FastHeader " n:ident " : " t:term : command =>
  `(axiom $n : $t)
