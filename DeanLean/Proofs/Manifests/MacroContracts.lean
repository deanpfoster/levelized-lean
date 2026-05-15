import DeanLean.Manifests.LeanEnvironment
import DeanLean.Defs.Manifests.MacroContracts
import Lean

/-! # Derivations for macro contracts

  Each derivation shows how our macro specs follow from Leo's Environment claims.
  DerivedConjecture auto-discovers the sorry dependencies.
-/

open Lean LeanEnvironment

-- ════════════════════════════════════════════════════════════
-- § Evidence macros: derivations
-- ════════════════════════════════════════════════════════════

-- ProvenTheorem: sorry-free thmInfo
theorem ProvenTheorem_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    ProvenTheoremSpec env n t := by
  intro env n t h_pre
  have := elab_theorem_creates_thmInfo  -- Leo: elab creates thmInfo
  have := real_proof_no_sorry           -- Leo: real proof has no sorry
  have := find_name_consistent          -- Leo: find? returns what was added
  sorry

-- TestedConjecture: sorry thmInfo
theorem TestedConjecture_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    TestedConjectureSpec env n t := by
  intro env n t h_pre
  have := elab_theorem_creates_thmInfo  -- Leo: elab creates thmInfo
  have := sorry_proof_detected          -- Leo: sorry proof has sorryAx
  sorry

-- FailingConjecture: sorry thmInfo, requires tests with failures
theorem FailingConjecture_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr) (passed total : Nat),
    FailingConjectureSpec env n t passed total := by
  intro env n t passed total h_total h_failing
  have := elab_theorem_creates_thmInfo
  have := sorry_proof_detected
  sorry

-- Test macro: always emits a def
theorem TestMacro_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (idx : Nat),
    TestMacroSpec env n idx := by
  intro env n idx
  have := elab_theorem_creates_thmInfo
  sorry

-- UnprovenConjecture: sorry thmInfo, no preconditions
theorem UnprovenConjecture_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    UnprovenConjectureSpec env n t := by
  intro env n t
  have := elab_theorem_creates_thmInfo
  have := sorry_proof_detected
  sorry

-- DecomposedConjecture: sorry thmInfo + all deps tested
theorem DecomposedConjecture_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    DecomposedConjectureSpec env n t := by
  intro env n t h_deriv h_all_tested
  have := elab_theorem_creates_thmInfo
  have := sorry_proof_detected
  sorry

-- DerivedConjecture: sorry thmInfo + auto-discovery
theorem DerivedConjecture_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    DerivedConjectureSpec env n t := by
  intro env n t h_deriv
  have := elab_theorem_creates_thmInfo
  have := sorry_proof_detected
  sorry

-- ════════════════════════════════════════════════════════════
-- § Other macros: derivations
-- ════════════════════════════════════════════════════════════

-- Signature: check type or create axiom
theorem Signature_is_correct_derivation :
    ∀ (envBefore envAfter : Environment) (n : Name) (t : Expr),
    SignatureSpec envBefore envAfter n t := by
  intro envBefore envAfter n t
  unfold SignatureSpec
  match h : envBefore.find? n with
  | some ci =>
    -- Function exists: Signature checks the type
    have := find_name_consistent
    sorry
  | none =>
    -- Function missing: Signature creates axiom
    have := elab_axiom_creates_axiomInfo
    sorry

-- FastHeader: creates axiom
theorem FastHeader_is_correct_derivation :
    ∀ (envAfter : Environment) (n : Name) (t : Expr),
    FastHeaderSpec envAfter n t := by
  intro envAfter n t
  have := elab_axiom_creates_axiomInfo
  sorry

-- VerifyAxiom: checks proof exists
theorem VerifyAxiom_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    VerifyAxiomSpec env n t := by
  intro env n t
  have := find_name_consistent
  sorry

-- Wrap: creates def referencing target
theorem Wrap_is_correct_derivation :
    ∀ (envAfter : Environment) (n target : Name),
    WrapSpec envAfter n target := by
  intro envAfter n target
  have := elab_preserves_others
  sorry

-- ════════════════════════════════════════════════════════════
-- § Cross-cutting: derivations
-- ════════════════════════════════════════════════════════════

-- Evidence ordering
theorem evidence_levels_are_distinguishable_derivation :
    ∀ (env : Environment), EvidenceOrderingInvariant env := by
  intro env
  have := real_proof_no_sorry
  have := sorry_proof_detected
  constructor
  · intro n h_proof
    match h : env.find? n with
    | some ci =>
      have := real_proof_no_sorry
      sorry
    | none => trivial
  · intro n h_test
    match h : env.find? n with
    | some ci =>
      have := sorry_proof_detected
      sorry
    | none => trivial

-- Strict ordering
theorem strict_ordering_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    StrictOrderingSpec env n t := by
  intro env n t h_decomposed
  -- DecomposedConjecture requirements include _derivation which implies testability
  sorry

-- Redundancy
theorem redundancy_works_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    RedundancySpec env n t := by
  intro env n t h_exists
  have := find_name_consistent
  sorry

-- Fast mode
theorem fast_mode_works_derivation :
    ∀ (envAfter : Environment) (n : Name) (t : Expr),
    FastModeSpec envAfter n t := by
  intro envAfter n t
  have := elab_axiom_creates_axiomInfo
  sorry

-- Promotion
theorem promotion_works_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    PromotionSpec env n t := by
  intro env n t
  have := real_proof_no_sorry
  have := find_name_consistent
  sorry

-- Vacuous test detection
theorem vacuous_test_detected_derivation :
    ∀ (env : Environment) (n : Name),
    VacuousTestSpec env n := by
  intro env n
  sorry
