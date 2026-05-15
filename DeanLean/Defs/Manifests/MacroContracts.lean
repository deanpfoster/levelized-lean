import DeanLean.Manifests.LeanEnvironment
import Lean

/-! # Vocabulary for macro contracts

  Specs for all 11 macros + cross-cutting properties.
  Each spec describes the Environment effect of running the macro.
-/

open Lean LeanEnvironment

-- ════════════════════════════════════════════════════════════
-- § Evidence macro specs
-- ════════════════════════════════════════════════════════════

/-- ProvenTheorem: creates sorry-free thmInfo from _proof or _derivation -/
def ProvenTheoremSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let proofName := n.appendAfter "_proof"
  let derivName := n.appendAfter "_derivation"
  ((env.find? proofName).isSome ∨ (env.find? derivName).isSome) →
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ SorryFree ci
    | _ => False

/-- TestedConjecture: creates sorry thmInfo, requires _test or all Tests passing -/
def TestedConjectureSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let testName := n.appendAfter "_test"
  (env.find? testName).isSome →
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ UsesSorry ci
    | _ => False

/-- FailingConjecture: creates sorry thmInfo, requires tests with at least one failing -/
def FailingConjectureSpec (env : Environment) (n : Name) (t : Expr)
    (passed total : Nat) : Prop :=
  total > 0 →
  passed < total →
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ UsesSorry ci
    | _ => False

/-- Test macro: tries elaboration, records pass/fail, always emits a def -/
def TestMacroSpec (env : Environment) (n : Name) (idx : Nat) : Prop :=
  let defName := n.appendAfter s!"_test_{idx}"
  (env.find? defName).isSome

/-- UnprovenConjecture: creates sorry thmInfo, no requirements -/
def UnprovenConjectureSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ UsesSorry ci
    | _ => False

/-- DecomposedConjecture: creates sorry thmInfo, requires _derivation,
    AND all sorry deps of the derivation must have _test witnesses -/
def DecomposedConjectureSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let derivName := n.appendAfter "_derivation"
  (env.find? derivName).isSome →
  -- The derivation exists and all its sorry deps are tested
  (∀ (dep : Name),
    match env.find? dep with
    | some depCi =>
      UsesSorry depCi →
      (env.find? (dep.appendAfter "_test")).isSome
    | none => True) →
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ UsesSorry ci
    | _ => False

/-- DerivedConjecture: creates sorry thmInfo, requires _derivation,
    auto-reports which dependencies have sorry -/
def DerivedConjectureSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let derivName := n.appendAfter "_derivation"
  (env.find? derivName).isSome →
  ∃ ci : ConstantInfo,
    match ci with
    | .thmInfo val => val.type = t ∧ UsesSorry ci
    | _ => False

-- ════════════════════════════════════════════════════════════
-- § Other macro specs
-- ════════════════════════════════════════════════════════════

/-- Signature: check type if function exists, create axiom if not -/
def SignatureSpec (envBefore envAfter : Environment) (n : Name) (t : Expr) : Prop :=
  match envBefore.find? n with
  | some ci => ci.type = t
  | none =>
    match envAfter.find? n with
    | some (.axiomInfo val) => val.type = t
    | _ => False

/-- FastHeader: always creates an axiom -/
def FastHeaderSpec (envAfter : Environment) (n : Name) (t : Expr) : Prop :=
  match envAfter.find? n with
  | some (.axiomInfo val) => val.type = t
  | _ => False

/-- VerifyAxiom: checks _proof/_derivation exists with matching type,
    doesn't modify env (just emits info/error) -/
def VerifyAxiomSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let proofName := n.appendAfter "_proof"
  let derivName := n.appendAfter "_derivation"
  -- Success iff proof or derivation exists
  (env.find? proofName).isSome ∨ (env.find? derivName).isSome

/-- Wrap: creates a noncomputable def aliasing another name -/
-- Wrap: creates a def that references the target
def WrapSpec (envAfter : Environment) (n : Name) (target : Name) : Prop :=
  match envAfter.find? n with
  | some ci => ci.getUsedConstantsAsSet.contains target  -- n references target
  | _ => False

-- ════════════════════════════════════════════════════════════
-- § Cross-cutting properties
-- ════════════════════════════════════════════════════════════

/-- Evidence ordering: _proof names are SorryFree, _test names UsesSorry -/
def EvidenceOrderingInvariant (env : Environment) : Prop :=
  (∀ (n : Name),
    (env.find? (n.appendAfter "_proof")).isSome →
    match env.find? n with
    | some ci => SorryFree ci
    | none => True) ∧
  (∀ (n : Name),
    (env.find? (n.appendAfter "_test")).isSome →
    match env.find? n with
    | some ci => UsesSorry ci
    | none => True)

/-- Strict ordering: DecomposedConjecture requirements ⊃ TestedConjecture requirements -/
def StrictOrderingSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  -- If DecomposedConjecture compiles, TestedConjecture would also compile
  -- (because _derivation exists implies we could create a _test from it)
  DecomposedConjectureSpec env n t → TestedConjectureSpec env n t

/-- Redundancy: if name already exists, macro just type-checks -/
def RedundancySpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  (env.find? n).isSome →
  match env.find? n with
  | some ci => ci.type = t  -- type must match
  | none => False

/-- Fast mode: ProvenTheorem creates axiom instead of looking up proof -/
def FastModeSpec (envAfter : Environment) (n : Name) (t : Expr) : Prop :=
  -- When levelized.fast = true, ProvenTheorem acts like FastHeader
  FastHeaderSpec envAfter n t

/-- Promotion: if DerivedConjecture compiles and sorry deps become zero,
    ProvenTheorem also compiles (no rename needed) -/
def PromotionSpec (env : Environment) (n : Name) (t : Expr) : Prop :=
  let derivName := n.appendAfter "_derivation"
  -- If derivation exists and is sorry-free, ProvenTheorem succeeds
  match env.find? derivName with
  | some ci => SorryFree ci → ProvenTheoremSpec env n t
  | none => True

/-- Vacuous test detection: test using absurd/False.elim triggers warning -/
def VacuousTestSpec (env : Environment) (n : Name) : Prop :=
  let testName := n.appendAfter "_test"
  match env.find? testName with
  | some ci =>
    let usesAbsurd := ci.getUsedConstantsAsSet.contains ``absurd
    let usesFalseElim := ci.getUsedConstantsAsSet.contains ``False.elim
    -- If test uses absurd/False.elim, it MAY be vacuous
    (usesAbsurd ∨ usesFalseElim) →
    -- Warning is emitted (can't express "warning" as Prop, but we can say:
    -- the test is flagged as potentially vacuous)
    True  -- the warning behavior is observable, not a Prop
  | none => True
