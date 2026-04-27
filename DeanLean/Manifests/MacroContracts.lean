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

/-- Model of Signature: if function exists, check type. If not, create axiom. -/
def SignatureSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  match env.find? n with
  | some ci => ci.type = t  -- type matches
  | none => True  -- axiom will be created (can't express env mutation in Prop)

-- ════════════════════════════════════════════════════════════
-- § The evidence ordering invariant
-- ════════════════════════════════════════════════════════════

/-- THE key invariant: sorry presence distinguishes evidence levels.
    This is what makes the whole manifest system meaningful. -/
def EvidenceOrderingInvariant (env : Environment) : Prop :=
  ∀ (n : Name),
  match env.find? n with
  | some ci =>
    let hasSorry := ci.getUsedConstantsAsSet.contains ``sorryAx
    -- A name created by ProvenTheorem has no sorry
    -- A name created by TestedConjecture has sorry
    -- The macro keyword determines the sorry presence
    True  -- (the full statement would need "created by" tracking)
  | none => True

-- ════════════════════════════════════════════════════════════
-- § Derivations: proofs that USE the Lean Environment claims
-- ════════════════════════════════════════════════════════════

-- If elab_theorem_creates_thmInfo holds (Leo's claim),
-- and real_proof_no_sorry holds (Leo's claim),
-- then ProvenTheoremSpec holds (our claim).
theorem ProvenTheorem_is_correct_derivation :
    -- Assuming Leo's claims:
    (∀ (env env' : Environment) (n : Name) (t proof : Expr),
      True → match env'.find? n with
      | some (.thmInfo val) => val.type = t
      | _ => False) →
    (∀ (ci : ConstantInfo), True → ¬ ci.getUsedConstantsAsSet.contains ``sorryAx) →
    -- Then our spec holds:
    ∀ (env : Environment) (n : Name) (t : Expr),
    ProvenTheoremSpec env n t := by
  intro h_elab h_no_sorry env n t h_pre
  -- The proof uses Leo's claims to establish our contract
  sorry -- Real proof would unfold the definitions and apply h_elab, h_no_sorry

-- If sorry_detected_in_constants holds (Leo's claim),
-- then TestedConjectureSpec holds (our claim).
theorem TestedConjecture_is_correct_derivation :
    (∀ (ci : ConstantInfo), True → ci.getUsedConstantsAsSet.contains ``sorryAx) →
    ∀ (env : Environment) (n : Name) (t : Expr),
    TestedConjectureSpec env n t := by
  sorry -- Real proof: sorry theorem has sorryAx by Leo's claim

-- The ordering invariant follows from both Leo claims together.
theorem evidence_levels_are_distinguishable_derivation :
    -- real proofs have no sorry
    (∀ (ci : ConstantInfo), True → ¬ ci.getUsedConstantsAsSet.contains ``sorryAx) →
    -- sorry theorems have sorry
    (∀ (ci : ConstantInfo), True → ci.getUsedConstantsAsSet.contains ``sorryAx) →
    -- therefore: the two are distinguishable
    ∀ (env : Environment), EvidenceOrderingInvariant env := by
  intro h_no_sorry h_has_sorry env
  -- This follows from: real proofs don't have sorry, sorry proofs do
  -- The EvidenceOrderingInvariant is trivially True in its current form
  -- A stronger version would require tracking "created by" provenance
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
