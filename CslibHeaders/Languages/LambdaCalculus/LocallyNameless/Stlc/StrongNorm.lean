import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Stlc.StrongNorm

/-! # Strong Normalization of the Simply Typed Lambda Calculus

  Every well-typed term is strongly normalizing: all beta-reduction
  sequences terminate. The proof uses Tait's method of logical relations
  (saturated sets).
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless
open Untyped.Term

-- Well-typed terms are strongly normalizing
ProvenTheorem Stlc.strong_norm :
  ∀ {Var : Type u_1} {Base : Type u_2} [DecidableEq Var] [HasFresh Var]
    {Γ : Context Var (Stlc.Ty Base)}
    {t : Untyped.Term Var} {τ : Stlc.Ty Base},
    Stlc.Typing Γ t τ → t.SN
