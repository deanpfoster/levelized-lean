import DeanLean.Basic
import DeanLean.Defs.Manifests.MacroContracts
import DeanLean.Proofs.Manifests.MacroContracts

/-! # Macro Contracts — what our manifest system guarantees

  Vocabulary in Defs/Manifests/MacroContracts.lean (13 specs).
  Derivations in Proofs/Manifests/MacroContracts.lean.

  11 macros. 7 cross-cutting properties. All specified.
-/

open Lean LeanEnvironment

-- ════════════════════════════════════════════════════════════
-- § Evidence macros
-- ════════════════════════════════════════════════════════════

DerivedConjecture ProvenTheorem_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    ProvenTheoremSpec env n t

DerivedConjecture TestedConjecture_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    TestedConjectureSpec env n t

DerivedConjecture FailingConjecture_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr) (passed total : Nat),
    FailingConjectureSpec env n t passed total

DerivedConjecture TestMacro_is_correct :
    ∀ (env : Environment) (n : Name) (idx : Nat),
    TestMacroSpec env n idx

DerivedConjecture UnprovenConjecture_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    UnprovenConjectureSpec env n t

DerivedConjecture DecomposedConjecture_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    DecomposedConjectureSpec env n t

DerivedConjecture DerivedConjecture_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    DerivedConjectureSpec env n t

-- ════════════════════════════════════════════════════════════
-- § Other macros
-- ════════════════════════════════════════════════════════════

DerivedConjecture Signature_is_correct :
    ∀ (envBefore envAfter : Environment) (n : Name) (t : Expr),
    SignatureSpec envBefore envAfter n t

DerivedConjecture FastHeader_is_correct :
    ∀ (envAfter : Environment) (n : Name) (t : Expr),
    FastHeaderSpec envAfter n t

DerivedConjecture VerifyAxiom_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    VerifyAxiomSpec env n t

DerivedConjecture Wrap_is_correct :
    ∀ (envAfter : Environment) (n target : Name),
    WrapSpec envAfter n target

-- ════════════════════════════════════════════════════════════
-- § Cross-cutting properties
-- ════════════════════════════════════════════════════════════

DerivedConjecture evidence_levels_are_distinguishable :
    ∀ (env : Environment), EvidenceOrderingInvariant env

DerivedConjecture strict_ordering :
    ∀ (env : Environment) (n : Name) (t : Expr),
    StrictOrderingSpec env n t

DerivedConjecture redundancy_works :
    ∀ (env : Environment) (n : Name) (t : Expr),
    RedundancySpec env n t

DerivedConjecture fast_mode_works :
    ∀ (envAfter : Environment) (n : Name) (t : Expr),
    FastModeSpec envAfter n t

DerivedConjecture promotion_works :
    ∀ (env : Environment) (n : Name) (t : Expr),
    PromotionSpec env n t

DerivedConjecture vacuous_test_detected :
    ∀ (env : Environment) (n : Name),
    VacuousTestSpec env n
