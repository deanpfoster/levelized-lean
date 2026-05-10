import Lean

/-! # Lean Manifests macros for CSLib -/

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

macro "ExternalTheorem " n:ident " := " src:term " : " t:term : command =>
  `(set_option linter.unusedVariables false in
    noncomputable def $n : $t := $src)

macro "CheckTheorem " src:term " : " t:term : command =>
  `(set_option linter.unusedVariables false in
    noncomputable example : $t := $src)

-- Vocabulary: define-or-verify.
-- If val elaborates: check that n resolves to the same constant.
-- If val doesn't elaborate: define n := val.
open Lean Elab Command Term in
elab "Vocabulary " n:ident " := " val:term : command => do
  let stx ← `(
    set_option linter.unusedVariables false in
    noncomputable example := $val)
  try
    elabCommand stx
    -- val exists. Now verify n refers to the same thing.
    -- Elaborate both in term mode and compare the resulting expressions.
    let nExpr ← liftTermElabM <| do
      let e ← elabTerm (← `($n)) none
      instantiateMVars e
    let vExpr ← liftTermElabM <| do
      let e ← elabTerm val none
      instantiateMVars e
    -- Extract the head constant from each
    let nHead := nExpr.getAppFn.constName?
    let vHead := vExpr.getAppFn.constName?
    match nHead, vHead with
    | some nn, some vn =>
      if nn != vn then
        throwError s!"Vocabulary mismatch: '{n.getId}' resolves to '{nn}' but value resolves to '{vn}'"
    | _, _ => pure () -- Can't compare, just accept
  catch e =>
    -- val didn't elaborate — might be because n doesn't exist yet
    -- Try defining it
    try
      elabCommand (← `(noncomputable def $n := $val))
    catch _ =>
      throw e
