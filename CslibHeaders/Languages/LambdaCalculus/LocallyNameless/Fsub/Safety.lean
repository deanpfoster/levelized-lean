import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.Reduction
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Fsub.Safety

/-! # System F-sub -- Type Safety

  The two fundamental theorems:
  - Preservation: call-by-value reduction preserves typing
  - Progress: a well-typed closed term is either a value or can step
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Fsub

-- Preservation: reduction preserves typing
ProvenTheorem Typing.preservation :
  ∀ {Var : Type u_1} [HasFresh Var] [inst : DecidableEq Var]
    {t : Term Var} {Γ : Env Var} {τ : Ty Var}
    {t' : Term Var},
    Typing Γ t τ → t.Red t' → Typing Γ t' τ

-- Progress: a well-typed closed term is a value or can step
ProvenTheorem Typing.progress :
  ∀ {Var : Type u_1} [HasFresh Var] [inst : DecidableEq Var]
    {t : Term Var} {τ : Ty Var},
    Typing [] t τ → t.Value ∨ ∃ t', t.Red t'
