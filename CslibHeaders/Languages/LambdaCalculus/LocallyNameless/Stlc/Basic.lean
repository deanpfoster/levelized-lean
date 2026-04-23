import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic

/-! # Simply Typed Lambda Calculus -- Definitions and Basic Properties

  Vocabulary:
    Stlc.Ty      -- simple types (base types and arrow types)
    Stlc.Typing  -- extrinsic typing derivation (Gamma |- t : tau)

  Typing is preserved under context permutation and opening.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless
open Untyped.Term

-- Typing is preserved under context permutation
ProvenTheorem Stlc.Typing.perm :
  ∀ {Var : Type u_1} {Base : Type u_2}
    {Γ Δ : Context Var (Stlc.Ty Base)}
    {t : Untyped.Term Var} {τ : Stlc.Ty Base},
    Stlc.Typing Γ t τ → List.Perm Γ Δ → Stlc.Typing Δ t τ

-- Typing preservation for opening
ProvenTheorem Stlc.Typing.preservation_open :
  ∀ {Var : Type u_1} {Base : Type u_2} [DecidableEq Var]
    {Γ : Context Var (Stlc.Ty Base)} [HasFresh Var]
    {σ : Stlc.Ty Base} {m : Untyped.Term Var}
    {τ : Stlc.Ty Base} {n : Untyped.Term Var}
    {xs : Finset Var},
    (∀ x ∉ xs,
      Stlc.Typing (⟨x, σ⟩ :: Γ)
        (m.open' (Untyped.Term.fvar x)) τ) →
    Stlc.Typing Γ n σ →
    Stlc.Typing Γ (m.open' n) τ
