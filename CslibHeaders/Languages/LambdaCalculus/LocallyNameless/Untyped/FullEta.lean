import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

/-! # Full Eta Reduction for the Lambda Calculus

  Vocabulary:
    Eta     -- single eta reduction step (lambda x. M x -> M when x not free in M)
    FullEta -- full eta reduction (congruence closure of Eta)

  Multi-step reduction is the reflexive-transitive closure.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Term

-- Left congruence for multi-step eta reduction
ProvenTheorem FullEta.redex_app_l_cong :
  ∀ {Var : Type u_1} {M M' N : Term Var},
    Relation.ReflTransGen FullEta M M' → N.LC →
    Relation.ReflTransGen FullEta (M.app N) (M'.app N)

-- Right congruence for multi-step eta reduction
ProvenTheorem FullEta.redex_app_r_cong :
  ∀ {Var : Type u_1} {M M' N : Term Var},
    Relation.ReflTransGen FullEta M M' → N.LC →
    Relation.ReflTransGen FullEta (N.app M) (N.app M')

-- Abstraction congruence for multi-step eta reduction
ProvenTheorem FullEta.redex_abs_cong :
  ∀ {Var : Type u_1} [HasFresh Var] [DecidableEq Var]
    {M M' : Term Var} (xs : Finset Var),
    (∀ x ∉ xs,
      Relation.ReflTransGen FullEta
        (M.open' (fvar x)) (M'.open' (fvar x))) →
    M.abs.LC →
    Relation.ReflTransGen FullEta M.abs M'.abs
