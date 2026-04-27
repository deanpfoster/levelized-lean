import DeanLean.Basic
import DeanLean.Tests.ManifestTests
import DeanLean.Tests.EnvironmentTests
import Lean

/-! # Manifest for the Manifest System

  Specifies what our macros do to the Lean Environment monad.

  Each macro in Basic.lean runs in CommandElabM, which is:
    ReaderT Context $ StateRefT State $ EIO Exception

  The observable effect: adding declarations to the Environment.
  We specify: given an environment with certain names, after the
  macro runs, what names exist and what are their types?

  Claims about Environment state: real Lean Prop types.
  Claims about compilation failure: typed as True (can't express).
-/

open Lean ProvenTheoremTests TestedConjectureTests DecomposedConjectureTests
     DerivedConjectureTests SignatureTests RedundancyTests VerifyAxiomTests
     OrderingTests

-- ════════════════════════════════════════════════════════════
-- § ProvenTheorem: Environment effects
-- ════════════════════════════════════════════════════════════

-- After ProvenTheorem, the name exists in the environment as a theorem
-- and its type matches the declared type.
TestedConjecture ProvenTheorem_adds_theorem_to_env :
    ∀ (env : Environment),
    (env.find? `ProvenTheoremTests.add_zero).isSome →
    match env.find? `ProvenTheoremTests.add_zero with
    | some (.thmInfo _) => True
    | _ => False

-- The theorem created by ProvenTheorem has the same type as the proof
TestedConjecture ProvenTheorem_type_matches_proof :
    ∀ (env : Environment),
    match env.find? `ProvenTheoremTests.add_zero, env.find? `ProvenTheoremTests.add_zero_proof with
    | some ci1, some ci2 => ci1.type == ci2.type
    | _, _ => false

-- ProvenTheorem from _derivation also creates a theorem
TestedConjecture ProvenTheorem_derivation_creates_theorem :
    ∀ (env : Environment),
    (env.find? `ProvenTheoremTests.mul_one).isSome →
    match env.find? `ProvenTheoremTests.mul_one with
    | some (.thmInfo _) => True
    | _ => False

-- Fast mode creates an axiom, not a theorem
TestedConjecture ProvenTheorem_fast_creates_axiom :
    ∀ (env : Environment),
    (env.find? `ProvenTheoremTests.fast_add_comm).isSome →
    match env.find? `ProvenTheoremTests.fast_add_comm with
    | some (.axiomInfo _) => True
    | _ => False

-- Compilation-failure claims
UnprovenConjecture ProvenTheorem_fails_without_proof :
    True -- env.find? (name ++ "_proof") = none → macro throws error
UnprovenConjecture ProvenTheorem_type_mismatch_fails :
    True -- proof.type ≠ declared type → kernel rejects

-- ════════════════════════════════════════════════════════════
-- § TestedConjecture: Environment effects
-- ════════════════════════════════════════════════════════════

-- Creates a theorem (with sorry) in the environment
TestedConjecture TestedConjecture_adds_sorry_theorem :
    ∀ (env : Environment),
    (env.find? `TestedConjectureTests.all_nats_ge_zero).isSome →
    match env.find? `TestedConjectureTests.all_nats_ge_zero with
    | some (.thmInfo _) => True
    | _ => False

-- The theorem uses sorry (its constants include sorryAx)
TestedConjecture TestedConjecture_theorem_has_sorry :
    ∀ (env : Environment),
    match env.find? `TestedConjectureTests.all_nats_ge_zero with
    | some ci => ci.getUsedConstantsAsSet.contains ``sorryAx
    | none => false

-- Compilation-failure claims
UnprovenConjecture TestedConjecture_fails_without_test :
    True -- env.find? (name ++ "_test") = none → macro throws error

-- ════════════════════════════════════════════════════════════
-- § Signature: Environment effects
-- ════════════════════════════════════════════════════════════

-- For existing functions: doesn't add anything new, just checks
TestedConjecture Signature_existing_no_new_decl :
    ∀ (env : Environment),
    (env.find? `SignatureTests.myAdd).isSome →
    match env.find? `SignatureTests.myAdd with
    | some (.defnInfo _) => True  -- still a def, not changed to axiom
    | _ => False

-- For missing functions: creates an axiom
TestedConjecture Signature_missing_creates_axiom :
    ∀ (env : Environment),
    (env.find? `SignatureTests.ghostFunction).isSome →
    match env.find? `SignatureTests.ghostFunction with
    | some (.axiomInfo _) => True
    | _ => False

-- ════════════════════════════════════════════════════════════
-- § DerivedConjecture: Environment effects
-- ════════════════════════════════════════════════════════════

-- Creates a sorry theorem
TestedConjecture DerivedConjecture_adds_sorry_theorem :
    ∀ (env : Environment),
    match env.find? `DerivedConjectureTests.uses_magic with
    | some ci => ci.getUsedConstantsAsSet.contains ``sorryAx
    | none => false

-- The derivation itself does NOT use sorry directly
-- (it uses theorems that have sorry, but the derivation is real)
TestedConjecture DerivedConjecture_derivation_is_real :
    ∀ (env : Environment),
    match env.find? `DerivedConjectureTests.uses_magic_derivation with
    | some ci => !ci.getUsedConstantsAsSet.contains ``sorryAx
    | none => true

-- ════════════════════════════════════════════════════════════
-- § VerifyAxiom: Environment effects
-- ════════════════════════════════════════════════════════════

-- VerifyAxiom doesn't add anything to the environment
-- (it just checks and emits a message)
UnprovenConjecture VerifyAxiom_no_env_change :
    True -- env after VerifyAxiom = env before (modulo example)

-- ════════════════════════════════════════════════════════════
-- § Redundancy: Environment effects
-- ════════════════════════════════════════════════════════════

-- Redundant ProvenTheorem doesn't create a second declaration
TestedConjecture redundancy_no_duplicate :
    ∀ (env : Environment),
    (env.find? `RedundancyTests.redundancy_example).isSome →
    match env.find? `RedundancyTests.redundancy_example with
    | some (.thmInfo _) => True  -- still the original theorem
    | _ => False

-- ════════════════════════════════════════════════════════════
-- § Evidence ordering: Environment invariants
-- ════════════════════════════════════════════════════════════

-- ProvenTheorem's result has no sorry in its constant set
TestedConjecture proven_has_no_sorry :
    ∀ (env : Environment),
    match env.find? `ProvenTheoremTests.add_zero with
    | some ci => !ci.getUsedConstantsAsSet.contains ``sorryAx
    | none => true

-- TestedConjecture's result HAS sorry
TestedConjecture tested_has_sorry :
    ∀ (env : Environment),
    match env.find? `TestedConjectureTests.all_nats_ge_zero with
    | some ci => ci.getUsedConstantsAsSet.contains ``sorryAx
    | none => false

-- This IS the formal distinction: ● has no sorry, ◐ has sorry
TestedConjecture evidence_ordering_is_sorry_presence :
    ∀ (env : Environment),
    let provenHasSorry := match env.find? `ProvenTheoremTests.add_zero with
      | some ci => ci.getUsedConstantsAsSet.contains ``sorryAx | none => false
    let testedHasSorry := match env.find? `TestedConjectureTests.all_nats_ge_zero with
      | some ci => ci.getUsedConstantsAsSet.contains ``sorryAx | none => false
    -- Proven has NO sorry, Tested HAS sorry
    !provenHasSorry ∧ testedHasSorry
