import Lean

/-! # Levelized Lean macros for CSLib headers -/

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

-- Vocabulary: define-or-verify via elaboration (not env.find?).
-- Uses try/catch so `open` namespaces work correctly.
open Lean Elab Command in
elab "Vocabulary " n:ident " := " val:term : command => do
  try
    elabCommand (← `(
      set_option linter.unusedVariables false in
      noncomputable example := $val))
  catch _ =>
    elabCommand (← `(noncomputable def $n := $val))
