import DeanLean.Basic
import Lean

/-! # Manifest for the Lean Environment API

  The slice of Lean's 200K+ line codebase that our macros depend on.
  These claims are TRUSTED — we treat them as axioms about Leo's code.
  If any are wrong, our macro proofs would be unsound.

  ## What we use from Lean

  Types: Environment, Name, Expr, ConstantInfo, ConstantVal,
         TheoremVal, AxiomVal, DefinitionVal
  Operations: Environment.find?, ConstantInfo.type, ConstantInfo.name,
              ConstantInfo.getUsedConstantsAsSet
  Monad: CommandElabM = ReaderT Context $ StateRefT State $ EIO Exception
  Effects: getEnv, elabCommand, throwError, logInfo, logWarning

  We don't manifest ALL of these — just the properties we need to
  prove our macro contracts correct.
-/

open Lean

namespace LeanEnvironment

-- ════════════════════════════════════════════════════════════
-- § ConstantInfo: structure of declarations
-- ════════════════════════════════════════════════════════════

-- Every ConstantInfo has a name
UnprovenConjecture ci_has_name :
    ∀ (ci : ConstantInfo), ci.name = ci.toConstantVal.name

-- Every ConstantInfo has a type
UnprovenConjecture ci_has_type :
    ∀ (ci : ConstantInfo), ci.type = ci.toConstantVal.type

-- thmInfo is a theorem (sorry or not)
UnprovenConjecture thmInfo_is_theorem :
    ∀ (val : TheoremVal), (ConstantInfo.thmInfo val).type = val.type

-- axiomInfo has no proof body
UnprovenConjecture axiomInfo_has_no_value :
    ∀ (val : AxiomVal), (ConstantInfo.axiomInfo val).value? = none

-- ════════════════════════════════════════════════════════════
-- § Environment.find?: lookup consistency
-- ════════════════════════════════════════════════════════════

-- find? returns the same name you looked up
UnprovenConjecture find_name_consistent :
    ∀ (env : Environment) (n : Name) (ci : ConstantInfo),
    env.find? n = some ci → ci.name = n

-- find? returns none for names not in the environment
-- (this is the definition of "not in the environment")
UnprovenConjecture find_none_means_absent :
    ∀ (env : Environment) (n : Name),
    env.find? n = none → ¬ env.contains n

-- ════════════════════════════════════════════════════════════
-- § Adding declarations: what elabCommand does
-- ════════════════════════════════════════════════════════════

-- After `theorem n : t := proof` is elaborated, find? n returns thmInfo
UnprovenConjecture elab_theorem_creates_thmInfo :
    ∀ (env env' : Environment) (n : Name) (t proof : Expr),
    -- if elaborating `theorem n : t := proof` transforms env to env'
    True →  -- (can't express "elab transforms env to env'" yet)
    match env'.find? n with
    | some (.thmInfo val) => val.type = t
    | _ => False

-- After `axiom n : t` is elaborated, find? n returns axiomInfo
UnprovenConjecture elab_axiom_creates_axiomInfo :
    ∀ (env env' : Environment) (n : Name) (t : Expr),
    True →
    match env'.find? n with
    | some (.axiomInfo val) => val.type = t
    | _ => False

-- Elaborating a declaration doesn't affect other names
UnprovenConjecture elab_preserves_others :
    ∀ (env env' : Environment) (n m : Name),
    n ≠ m →
    -- if elaborating something for n transforms env to env'
    True →
    env'.find? m = env.find? m

-- ════════════════════════════════════════════════════════════
-- § getUsedConstantsAsSet: sorry detection
-- ════════════════════════════════════════════════════════════

-- A theorem proven by `by sorry` has sorryAx in its used constants
UnprovenConjecture sorry_detected_in_constants :
    ∀ (ci : ConstantInfo),
    -- if ci was created by `theorem n : t := by sorry`
    True →
    ci.getUsedConstantsAsSet.contains ``sorryAx

-- A theorem with a real proof does NOT have sorryAx
UnprovenConjecture real_proof_no_sorry :
    ∀ (ci : ConstantInfo),
    -- if ci was created by `theorem n : t := real_proof` where real_proof has no sorry
    True →
    ¬ ci.getUsedConstantsAsSet.contains ``sorryAx

-- getUsedConstantsAsSet is transitive: if A uses B and B uses sorry, then A uses sorry
UnprovenConjecture sorry_is_transitive :
    ∀ (env : Environment) (a b : Name),
    match env.find? a, env.find? b with
    | some ciA, some ciB =>
      ciA.getUsedConstantsAsSet.contains b →
      ciB.getUsedConstantsAsSet.contains ``sorryAx →
      ciA.getUsedConstantsAsSet.contains ``sorryAx
    | _, _ => True

-- ════════════════════════════════════════════════════════════
-- § CommandElabM: the monad our macros run in
-- ════════════════════════════════════════════════════════════

-- throwError stops execution (no further env modifications)
UnprovenConjecture throwError_stops_execution :
    True -- ∀ action after throwError: not executed

-- elabCommand modifies the environment
UnprovenConjecture elabCommand_modifies_env :
    True -- the env after elabCommand may differ from env before

-- getEnv returns the current environment
UnprovenConjecture getEnv_is_current :
    True -- env ← getEnv reflects all prior elabCommand effects

-- ════════════════════════════════════════════════════════════
-- § Key invariant: sorry presence distinguishes evidence levels
-- ════════════════════════════════════════════════════════════

-- THE FUNDAMENTAL CLAIM that our entire evidence hierarchy rests on:
-- `sorryAx` in getUsedConstantsAsSet is a RELIABLE indicator of
-- whether a proof has unfinished obligations.

-- If this is wrong, ProvenTheorem and TestedConjecture are
-- indistinguishable, and the hierarchy collapses.

UnprovenConjecture sorry_is_reliable_indicator :
    ∀ (env : Environment) (n : Name),
    match env.find? n with
    | some ci =>
      -- sorry in constants ↔ proof has unfinished obligations
      ci.getUsedConstantsAsSet.contains ``sorryAx ↔
      True -- (the proof of n, or something it depends on, uses sorry)
    | none => True

end LeanEnvironment
