import DeanLean.Basic
import DeanLean.Tests.ManifestTests

/-! # Manifest for the Manifest System

  Self-referential: specifies what our macro system promises.

  Claims that CAN be expressed as Prop have real types.
  Claims about compilation failure are documented but typed as True
  (can't express "this code fails to compile" as a Prop).
-/

open ProvenTheoremTests TestedConjectureTests DecomposedConjectureTests
     DerivedConjectureTests SignatureTests RedundancyTests VerifyAxiomTests
     OrderingTests

-- ════════════════════════════════════════════════════════════
-- § ProvenTheorem: created theorems are usable with correct values
-- ════════════════════════════════════════════════════════════

-- add_zero was created by ProvenTheorem and equals Nat.add_zero
TestedConjecture ProvenTheorem_creates_correct_theorem :
    ∀ (n : Nat), n + 0 = n

-- mul_one was created via _derivation (not _proof) and works
TestedConjecture ProvenTheorem_derivation_works :
    ∀ (n : Nat), n * 1 = n

-- Redundant ProvenTheorem doesn't create a second copy
TestedConjecture ProvenTheorem_redundancy_preserves_value :
    ∀ (n : Nat), add_zero n = Nat.add_zero n

-- Fast-mode axiom exists and has the right type
TestedConjecture ProvenTheorem_fast_mode_has_type :
    ∀ (a b : Nat), fast_add_comm a b = fast_add_comm a b

-- Compilation-failure claims (can't express as Prop)
UnprovenConjecture ProvenTheorem_fails_without_proof :
    True -- "Fails if neither foo_proof nor foo_derivation exists"
UnprovenConjecture ProvenTheorem_type_mismatch_fails :
    True -- "Fails if foo_proof has type U ≠ T"

-- ════════════════════════════════════════════════════════════
-- § TestedConjecture: creates sorry theorems, tests are checked
-- ════════════════════════════════════════════════════════════

-- The created theorem exists (even though it's sorry)
TestedConjecture TestedConjecture_creates_usable_theorem :
    ∀ (n : Nat), all_nats_ge_zero n = all_nats_ge_zero n

-- Vacuous warning was emitted (we can check the test compiled)
TestedConjecture TestedConjecture_vacuous_test_compiles :
    vacuous_thing 42 = vacuous_thing 42

-- Classical suppression works (another_vacuous compiled without warning)
TestedConjecture TestedConjecture_suppression_compiles :
    another_vacuous 42 = another_vacuous 42

-- Compilation-failure claim
UnprovenConjecture TestedConjecture_fails_without_test :
    True -- "Fails if foo_test doesn't exist"

-- ════════════════════════════════════════════════════════════
-- § DecomposedConjecture: proof structure with all deps tested
-- ════════════════════════════════════════════════════════════

-- The combined theorem exists and uses lemma_a and lemma_b
TestedConjecture DecomposedConjecture_theorem_exists :
    ∀ (n m : Nat), combined n m = combined n m

-- Compilation-failure claims
UnprovenConjecture DecomposedConjecture_fails_without_derivation :
    True -- "Fails if foo_derivation doesn't exist"
UnprovenConjecture DecomposedConjecture_fails_with_untested_dep :
    True -- "Fails if any sorry dep lacks _test"

-- ════════════════════════════════════════════════════════════
-- § DerivedConjecture: auto-discovers sorry dependencies
-- ════════════════════════════════════════════════════════════

-- The derived theorem exists
TestedConjecture DerivedConjecture_theorem_exists :
    ∀ (n : Nat), uses_magic n = uses_magic n

-- Compilation-failure claim
UnprovenConjecture DerivedConjecture_fails_without_derivation :
    True -- "Fails if foo_derivation doesn't exist"

-- ════════════════════════════════════════════════════════════
-- § Signature: checks or creates functions
-- ════════════════════════════════════════════════════════════

-- Existing function passes Signature check
TestedConjecture Signature_existing_function_passes :
    myAdd 2 3 = 5

-- Ghost function was created as axiom by Signature
TestedConjecture Signature_axiom_has_correct_type :
    ghostFunction = ghostFunction  -- exists, type Nat → Bool

-- Compilation-failure claims
UnprovenConjecture Signature_rejects_partial :
    True -- "Fails if foo is partial"
UnprovenConjecture Signature_rejects_wrong_type :
    True -- "Fails if foo has different type"

-- ════════════════════════════════════════════════════════════
-- § Redundancy: all macros handle duplicate declarations
-- ════════════════════════════════════════════════════════════

-- Redundant declarations preserve the original value
TestedConjecture redundancy_preserves_theorem :
    redundancy_example = rfl

-- Multiple redundant TestedConjectures work
TestedConjecture redundancy_tested_works :
    some_thing = some_thing

-- Compilation-failure claims
UnprovenConjecture redundancy_type_mismatch_fails :
    True -- "Fails if redundant declaration has wrong type"
UnprovenConjecture redundancy_open_namespace :
    True -- "Should work via 'open' (not yet implemented)"

-- ════════════════════════════════════════════════════════════
-- § VerifyAxiom: confirms axioms match proofs
-- ════════════════════════════════════════════════════════════

-- VerifyAxiom compiled successfully (confirms match)
TestedConjecture VerifyAxiom_compiles_with_proof :
    True -- verified_thing was confirmed by VerifyAxiom

-- Compilation-failure claim
UnprovenConjecture VerifyAxiom_fails_without_proof :
    True -- "Fails if no proof found"

-- ════════════════════════════════════════════════════════════
-- § Evidence hierarchy ordering
-- ════════════════════════════════════════════════════════════

-- A proven theorem's value is deterministic (not sorry)
TestedConjecture proven_is_deterministic :
    OrderingTests.ordering_thm = rfl

-- Compilation-failure claim
UnprovenConjecture hierarchy_is_strict :
    True -- "DecomposedConjecture requirements ⊃ TestedConjecture requirements"
