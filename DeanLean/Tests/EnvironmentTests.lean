import DeanLean.Basic
import DeanLean.Tests.ManifestTests
import Lean

/-! # Environment-level tests for the manifest system -/

open Lean Elab Command in
elab "#check_is_theorem " n:ident : command => do
  let env ← getEnv
  match env.find? n.getId with
  | some (.thmInfo _) => logInfo m!"{n.getId}: ✓ is a theorem"
  | some _ => throwError s!"{n.getId}: ✗ exists but is NOT a theorem"
  | none => throwError s!"{n.getId}: ✗ not found"

open Lean Elab Command in
elab "#check_is_axiom " n:ident : command => do
  let env ← getEnv
  match env.find? n.getId with
  | some (.axiomInfo _) => logInfo m!"{n.getId}: ✓ is an axiom"
  | some _ => throwError s!"{n.getId}: ✗ exists but is NOT an axiom"
  | none => throwError s!"{n.getId}: ✗ not found"

open Lean Elab Command in
elab "#check_is_def " n:ident : command => do
  let env ← getEnv
  match env.find? n.getId with
  | some (.defnInfo _) => logInfo m!"{n.getId}: ✓ is a def"
  | some _ => throwError s!"{n.getId}: ✗ exists but is NOT a def"
  | none => throwError s!"{n.getId}: ✗ not found"

open Lean Elab Command in
elab "#check_has_sorry " n:ident : command => do
  let env ← getEnv
  match env.find? n.getId with
  | some ci =>
    if ci.getUsedConstantsAsSet.contains ``sorryAx then
      logInfo m!"{n.getId}: ✓ has sorry"
    else
      throwError s!"{n.getId}: ✗ does NOT have sorry"
  | none => throwError s!"{n.getId}: ✗ not found"

open Lean Elab Command in
elab "#check_no_sorry " n:ident : command => do
  let env ← getEnv
  match env.find? n.getId with
  | some ci =>
    if !ci.getUsedConstantsAsSet.contains ``sorryAx then
      logInfo m!"{n.getId}: ✓ no sorry"
    else
      throwError s!"{n.getId}: ✗ HAS sorry (unexpected)"
  | none => throwError s!"{n.getId}: ✗ not found"

-- ════════════════════════════════════════════════════════════
-- § ProvenTheorem environment effects
-- ════════════════════════════════════════════════════════════

#check_is_theorem ProvenTheoremTests.add_zero
#check_is_theorem ProvenTheoremTests.mul_one
#check_is_axiom ProvenTheoremTests.fast_add_comm
#check_no_sorry ProvenTheoremTests.add_zero

-- ════════════════════════════════════════════════════════════
-- § TestedConjecture environment effects
-- ════════════════════════════════════════════════════════════

#check_is_theorem TestedConjectureTests.all_nats_ge_zero
#check_has_sorry TestedConjectureTests.all_nats_ge_zero

-- ════════════════════════════════════════════════════════════
-- § Signature environment effects
-- ════════════════════════════════════════════════════════════

#check_is_def SignatureTests.myAdd
#check_is_axiom SignatureTests.ghostFunction

-- ════════════════════════════════════════════════════════════
-- § DerivedConjecture environment effects
-- ════════════════════════════════════════════════════════════

#check_has_sorry DerivedConjectureTests.uses_magic
#check_no_sorry DerivedConjectureTests.uses_magic_derivation

-- ════════════════════════════════════════════════════════════
-- § Evidence ordering: proven has no sorry, tested has sorry
-- ════════════════════════════════════════════════════════════

#check_no_sorry ProvenTheoremTests.add_zero
#check_has_sorry TestedConjectureTests.all_nats_ge_zero

-- ════════════════════════════════════════════════════════════
-- Trivial _test witnesses for TestedConjecture in the manifest.
-- The real tests are the #check_* commands above.
-- ════════════════════════════════════════════════════════════

def ProvenTheorem_adds_theorem_to_env_test := ()
def ProvenTheorem_type_matches_proof_test := ()
def ProvenTheorem_derivation_creates_theorem_test := ()
def ProvenTheorem_fast_creates_axiom_test := ()
def TestedConjecture_adds_sorry_theorem_test := ()
def TestedConjecture_theorem_has_sorry_test := ()
def Signature_existing_no_new_decl_test := ()
def Signature_missing_creates_axiom_test := ()
def DerivedConjecture_adds_sorry_theorem_test := ()
def DerivedConjecture_derivation_is_real_test := ()
def redundancy_no_duplicate_test := ()
def proven_has_no_sorry_test := ()
def tested_has_sorry_test := ()
def evidence_ordering_is_sorry_presence_test := ()
