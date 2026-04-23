import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

/-! # Properties of Locally Nameless Lambda Terms

  Key properties of substitution, opening, and local closure.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Term

-- Substitution of a fresh variable is the identity
ProvenTheorem subst_fresh :
  ∀ {Var : Type u_1} [inst : DecidableEq Var] (x : Var)
    (t sub : Term Var), x ∉ t.fv → t[x := sub] = t

-- Substitution commutes with opening by a free variable
ProvenTheorem subst_open_var :
  ∀ {Var : Type u_1} [inst : DecidableEq Var] [HasFresh Var]
    (x y : Var) (u e : Term Var), y ≠ x → u.LC →
    (e.open' (fvar x))[y := u] = e[y := u].open' (fvar x)

-- Substitution of LC terms preserves LC
ProvenTheorem subst_lc :
  ∀ {Var : Type u_1} [inst : DecidableEq Var] [HasFresh Var]
    {x : Var} {e u : Term Var}, e.LC → u.LC → e[x := u].LC

-- Beta reduction (opening) of LC terms preserves LC
ProvenTheorem beta_lc :
  ∀ {Var : Type u_1} [DecidableEq Var] [HasFresh Var]
    {M N : Term Var}, M.abs.LC → N.LC → (M.open' N).LC
