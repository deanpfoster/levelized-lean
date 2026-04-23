import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype

/-! # System F-sub -- Subtyping

  Vocabulary:
    Sub -- the subtyping relation

  Key results:
  - Subtype transitivity (the hardest metatheoretic property of F-sub)
  - Subtype reflexivity for well-formed types
  - Narrowing of subtypes
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Fsub

-- Subtyping is transitive
ProvenTheorem Sub.trans :
  ∀ {Var : Type u_1} [inst : DecidableEq Var]
    {Γ : Env Var} {σ τ δ : Ty Var},
    Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ

-- Subtyping is reflexive for well-formed types
ProvenTheorem Sub.refl :
  ∀ {Var : Type u_1} [inst : DecidableEq Var]
    {Γ : Env Var} {σ : Ty Var},
    Γ.Wf → Ty.Wf Γ σ → Sub Γ σ σ

-- Narrowing of subtypes
ProvenTheorem Sub.narrow :
  ∀ {Var : Type u_1} [inst : DecidableEq Var]
    {Γ Δ : Env Var} {σ τ δ δ' : Ty Var} {X : Var},
    Sub Δ δ δ' →
    Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ →
    Sub (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) σ τ
