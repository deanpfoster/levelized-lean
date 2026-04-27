import DeanLean.Basic
import Lean

/-! # Manifest for the Lean Environment API

  The slice of Lean's 200K+ line codebase that our macros depend on.
  These claims are TRUSTED — we treat them as axioms about Leo's code.
  If any are wrong, our macro proofs would be unsound.
-/

open Lean

namespace LeanEnvironment

-- ════════════════════════════════════════════════════════════
-- § Vocabulary: how we model elaboration effects
-- ════════════════════════════════════════════════════════════

-- "env' is env after adding a theorem n : t := proof"
def IsTheoremElaboration (env env' : Environment) (n : Name) (t proof : Expr) : Prop :=
  match env'.find? n with
  | some (.thmInfo val) => val.type = t
  | _ => False

/-- "env' is env after adding an axiom n : t" -/
def IsAxiomElaboration (env env' : Environment) (n : Name) (t : Expr) : Prop :=
  match env'.find? n with
  | some (.axiomInfo val) => val.type = t
  | _ => False

/-- "ci was created from a proof that uses sorry somewhere" -/
def UsesSorry (ci : ConstantInfo) : Prop :=
  ci.getUsedConstantsAsSet.contains ``sorryAx

/-- "ci was created from a proof that does NOT use sorry" -/
def SorryFree (ci : ConstantInfo) : Prop :=
  ¬ ci.getUsedConstantsAsSet.contains ``sorryAx

/-- "the proof body of ci directly invokes sorryAx" -/
def DirectlySorry (ci : ConstantInfo) : Prop :=
  match ci.value? (allowOpaque := true) with
  | some v => v.getUsedConstantsAsSet.contains ``sorryAx
  | none => False

-- ════════════════════════════════════════════════════════════
-- § ConstantInfo: structure of declarations
-- ════════════════════════════════════════════════════════════

UnprovenConjecture ci_has_name :
    ∀ (ci : ConstantInfo), ci.name = ci.toConstantVal.name

UnprovenConjecture ci_has_type :
    ∀ (ci : ConstantInfo), ci.type = ci.toConstantVal.type

UnprovenConjecture thmInfo_is_theorem :
    ∀ (val : TheoremVal), (ConstantInfo.thmInfo val).type = val.type

UnprovenConjecture axiomInfo_has_no_value :
    ∀ (val : AxiomVal), (ConstantInfo.axiomInfo val).value? = none

-- ════════════════════════════════════════════════════════════
-- § Environment.find?: lookup consistency
-- ════════════════════════════════════════════════════════════

UnprovenConjecture find_name_consistent :
    ∀ (env : Environment) (n : Name) (ci : ConstantInfo),
    env.find? n = some ci → ci.name = n

UnprovenConjecture find_none_means_absent :
    ∀ (env : Environment) (n : Name),
    env.find? n = none → ¬ env.contains n

-- ════════════════════════════════════════════════════════════
-- § Elaboration effects: what elabCommand does to the Environment
-- ════════════════════════════════════════════════════════════

-- Elaborating `theorem n : t := proof` creates a thmInfo with type t
UnprovenConjecture elab_theorem_creates_thmInfo :
    ∀ (env env' : Environment) (n : Name) (t proof : Expr),
    IsTheoremElaboration env env' n t proof →
    match env'.find? n with
    | some (.thmInfo val) => val.type = t
    | _ => False

-- Elaborating `axiom n : t` creates an axiomInfo with type t
UnprovenConjecture elab_axiom_creates_axiomInfo :
    ∀ (env env' : Environment) (n : Name) (t : Expr),
    IsAxiomElaboration env env' n t →
    match env'.find? n with
    | some (.axiomInfo val) => val.type = t
    | _ => False

-- Elaborating a declaration for n doesn't affect other names
UnprovenConjecture elab_preserves_others :
    ∀ (env env' : Environment) (n m : Name),
    n ≠ m →
    (IsTheoremElaboration env env' n sorry sorry ∨
     IsAxiomElaboration env env' n sorry) →
    env'.find? m = env.find? m

-- ════════════════════════════════════════════════════════════
-- § Sorry detection: getUsedConstantsAsSet
-- ════════════════════════════════════════════════════════════

-- A theorem whose proof is `by sorry` has sorryAx in used constants
UnprovenConjecture sorry_proof_detected :
    ∀ (ci : ConstantInfo),
    DirectlySorry ci → UsesSorry ci

-- A theorem whose proof has NO sorry anywhere is sorry-free
UnprovenConjecture real_proof_no_sorry :
    ∀ (ci : ConstantInfo),
    ¬ DirectlySorry ci →
    (∀ (dep : Name), ci.getUsedConstantsAsSet.contains dep → dep ≠ ``sorryAx) →
    SorryFree ci

-- Sorry is transitive through dependencies
UnprovenConjecture sorry_is_transitive :
    ∀ (env : Environment) (a b : Name),
    match env.find? a, env.find? b with
    | some ciA, some ciB =>
      ciA.getUsedConstantsAsSet.contains b →
      UsesSorry ciB →
      UsesSorry ciA
    | _, _ => True

-- ════════════════════════════════════════════════════════════
-- § CommandElabM: the monad
-- ════════════════════════════════════════════════════════════

-- throwError prevents subsequent env modifications.
-- This follows from Except.bind: error >>= f = error (by rfl).
-- CommandElabM is built on EIO which extends Except.
-- Therefore: if a macro calls throwError, bind short-circuits,
-- and no subsequent elabCommand modifies the environment.

-- This is PROVABLE (not an axiom about Leo's code):
theorem error_bind_is_error_proof {α β ε : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e) >>= f = Except.error e := rfl

ProvenTheorem error_bind_is_error :
    ∀ {α β ε : Type} (e : ε) (f : α → Except ε β),
    (Except.error e) >>= f = Except.error e

-- The connection to CommandElabM: throwError produces Except.error,
-- so by error_bind_is_error, subsequent actions don't execute.
-- The env state is managed by StateRefT, which only commits on success.
UnprovenConjecture throwError_preserves_env :
    ∀ (envBefore envAfter : Environment),
    -- If CommandElabM action resulted in error (threw)
    -- then envAfter = envBefore (state not committed)
    ∀ (n : Name), envBefore.find? n = envAfter.find? n

-- getEnv returns the environment reflecting all prior mutations
UnprovenConjecture getEnv_reflects_mutations :
    ∀ (env : Environment) (n : Name) (ci : ConstantInfo),
    -- if elabCommand added ci under name n, then getEnv finds it
    env.find? n = some ci →
    env.find? n = some ci  -- tautology, but states: getEnv is faithful

-- ════════════════════════════════════════════════════════════
-- § THE FUNDAMENTAL INVARIANT
-- ════════════════════════════════════════════════════════════

-- sorryAx presence in getUsedConstantsAsSet is a FAITHFUL indicator.
-- If ci.getUsedConstantsAsSet.contains ``sorryAx, then the proof
-- of ci (or something it transitively depends on) uses sorry.
-- If NOT, then the entire proof chain is sorry-free.

UnprovenConjecture sorry_is_reliable_indicator :
    ∀ (env : Environment) (n : Name),
    match env.find? n with
    | some ci =>
      -- sorry in constants ↔ proof has unfinished obligations
      UsesSorry ci ↔ (DirectlySorry ci ∨
        ∃ dep, ci.getUsedConstantsAsSet.contains dep ∧
          match env.find? dep with
          | some depCi => UsesSorry depCi
          | none => False)
    | none => True

end LeanEnvironment
