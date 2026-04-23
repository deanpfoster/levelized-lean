import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Stlc.Safety

/-! # Type Safety of the Simply Typed Lambda Calculus

  The two fundamental theorems:
  - Preservation: typing is invariant under full beta reduction
  - Progress: a well-typed closed term is either a value or can step
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless
open Untyped.Term

-- Preservation: full beta reduction preserves typing
ProvenTheorem Stlc.FullBeta.preservation :
  ∀ {Var : Type u_1} {Base : Type u_2} [HasFresh Var] [DecidableEq Var]
    {Γ : Context Var (Stlc.Ty Base)}
    {t : Untyped.Term Var} {τ : Stlc.Ty Base}
    {t' : Untyped.Term Var},
    Stlc.Typing Γ t τ → t.FullBeta t' → Stlc.Typing Γ t' τ

-- Progress: a well-typed closed term is a value or can step
ProvenTheorem Stlc.FullBeta.progress :
  ∀ {Var : Type u_1} {Base : Type u_2}
    {t : Untyped.Term Var} {τ : Stlc.Ty Base},
    Stlc.Typing [] t τ → t.Value ∨ ∃ t', t.FullBeta t'
