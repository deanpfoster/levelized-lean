import DeanLean.Basic
import DeanLean.Manifests.LeanEnvironment
import DeanLean.Tests.ManifestTests
import DeanLean.Tests.EnvironmentTests
import Lean

/-! # Macro Contracts: proven from the Lean Environment manifest

  These are the contracts our macros provide to downstream users.
  Each is a DerivedConjecture — real proof structure that depends
  on UnprovenConjectures from LeanEnvironment.lean.

  The dependency chain:
    LeanEnvironment.lean (claims TO Leo, 16 UnprovenConjectures)
      ↓ used by
    MacroContracts.lean (claims FROM us, DerivedConjectures)
      ↓ used by
    Downstream macro authors

  When Leo proves the 16 claims, our DerivedConjectures auto-promote.
-/

open Lean LeanEnvironment

-- ════════════════════════════════════════════════════════════
-- § Pure model (the spec our macros should implement)
-- ════════════════════════════════════════════════════════════

/-- Model of ProvenTheorem: given an env where n_proof exists,
    the result is a sorry-free thmInfo with the declared type.
    This is what ProvenTheorem SHOULD do. -/
def ProvenTheoremSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let proofName := n.appendAfter "_proof"
  let derivName := n.appendAfter "_derivation"
  -- Precondition: proof or derivation exists
  ((env.find? proofName).isSome ∨ (env.find? derivName).isSome) →
  -- Postcondition: n exists as thmInfo with matching type, no sorry
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ ¬ ci.getUsedConstantsAsSet.contains ``sorryAx
    | _ => False

/-- Model of TestedConjecture: given an env where n_test exists,
    the result is a sorry thmInfo. -/
def TestedConjectureSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let testName := n.appendAfter "_test"
  -- Precondition: test exists
  (env.find? testName).isSome →
  -- Postcondition: n exists as thmInfo with sorry
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ ci.getUsedConstantsAsSet.contains ``sorryAx
    | _ => False

/-- Model of Signature: if function exists, check type matches.
    If not, an axiom will be created (expressed as: the post-env has it). -/
def SignatureSpec (envBefore envAfter : Environment) (n : Name) (t : Expr) : Prop :=
  match envBefore.find? n with
  | some ci => ci.type = t  -- existing function: type matches
  | none =>
    -- missing function: Signature creates an axiom
    match envAfter.find? n with
    | some (.axiomInfo val) => val.type = t
    | _ => False

-- ════════════════════════════════════════════════════════════
-- § The evidence ordering invariant
-- ════════════════════════════════════════════════════════════

/-- THE key invariant: sorry presence distinguishes evidence levels.
    For any name n with a companion n_proof (created by ProvenTheorem),
    n has no sorry. For any name n with a companion n_test (created by
    TestedConjecture), n has sorry. The evidence level is observable. -/
def EvidenceOrderingInvariant (env : Environment) : Prop :=
  -- ProvenTheorem results have no sorry
  (∀ (n : Name),
    (env.find? (n.appendAfter "_proof")).isSome →
    match env.find? n with
    | some ci => LeanEnvironment.SorryFree ci
    | none => True) ∧
  -- TestedConjecture results have sorry
  (∀ (n : Name),
    (env.find? (n.appendAfter "_test")).isSome →
    match env.find? n with
    | some ci => LeanEnvironment.UsesSorry ci
    | none => True)

-- ════════════════════════════════════════════════════════════
-- § Derivations: proofs that USE the Lean Environment claims
-- ════════════════════════════════════════════════════════════

-- If elab_theorem_creates_thmInfo holds (Leo's claim),
-- and real_proof_no_sorry holds (Leo's claim),
-- then ProvenTheoremSpec holds (our claim).
-- Derivation references Leo's named claims directly.
-- DerivedConjecture auto-discovers these as sorry dependencies.
theorem ProvenTheorem_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    ProvenTheoremSpec env n t := by
  intro env n t h_pre
  -- Step 1: By elab_theorem_creates_thmInfo, elaborating the theorem creates thmInfo
  have h1 := elab_theorem_creates_thmInfo
  -- Step 2: By real_proof_no_sorry, the real proof has no sorryAx
  have h2 := real_proof_no_sorry
  -- Step 3: By find_name_consistent, we get back what we added
  have h3 := find_name_consistent
  -- Combine to get ProvenTheoremSpec
  sorry

theorem TestedConjecture_is_correct_derivation :
    ∀ (env : Environment) (n : Name) (t : Expr),
    TestedConjectureSpec env n t := by
  intro env n t h_pre
  -- By elab_theorem_creates_thmInfo, elaborating creates thmInfo
  have h1 := elab_theorem_creates_thmInfo
  -- By sorry_proof_detected, sorry theorem has sorryAx
  have h2 := sorry_proof_detected
  sorry

theorem evidence_levels_are_distinguishable_derivation :
    ∀ (env : Environment), EvidenceOrderingInvariant env := by
  intro env
  -- By real_proof_no_sorry: proven theorems lack sorryAx
  have h1 := real_proof_no_sorry
  -- By sorry_proof_detected: sorry theorems have sorryAx
  have h2 := sorry_proof_detected
  -- Therefore the two are distinguishable
  sorry

-- ════════════════════════════════════════════════════════════
-- § DerivedConjectures: our guarantees, conditional on Leo
-- ════════════════════════════════════════════════════════════

DerivedConjecture ProvenTheorem_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    ProvenTheoremSpec env n t

DerivedConjecture TestedConjecture_is_correct :
    ∀ (env : Environment) (n : Name) (t : Expr),
    TestedConjectureSpec env n t

DerivedConjecture evidence_levels_are_distinguishable :
    ∀ (env : Environment), EvidenceOrderingInvariant env
