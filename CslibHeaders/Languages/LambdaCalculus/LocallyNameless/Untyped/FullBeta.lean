import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

/-! # Full Beta Reduction for the Lambda Calculus

  Vocabulary:
    Beta     -- single beta reduction step
    FullBeta -- full beta reduction (congruence closure of Beta)

  Multi-step reduction is the reflexive-transitive closure.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Term

-- Left congruence for multi-step beta reduction
ProvenTheorem FullBeta.redex_app_l_cong :
  ∀ {Var : Type u_1} {M M' N : Term Var},
    Relation.ReflTransGen FullBeta M M' → N.LC →
    Relation.ReflTransGen FullBeta (M.app N) (M'.app N)

-- Right congruence for multi-step beta reduction
ProvenTheorem FullBeta.redex_app_r_cong :
  ∀ {Var : Type u_1} {M M' N : Term Var},
    Relation.ReflTransGen FullBeta M M' → N.LC →
    Relation.ReflTransGen FullBeta (N.app M) (N.app M')

-- Abstraction congruence for multi-step beta reduction
ProvenTheorem FullBeta.redex_abs_cong :
  ∀ {Var : Type u_1} {M M' : Term Var} [HasFresh Var] [DecidableEq Var]
    (xs : Finset Var),
    (∀ x ∉ xs,
      Relation.ReflTransGen FullBeta (M.open' (fvar x)) (M'.open' (fvar x))) →
    Relation.ReflTransGen FullBeta M.abs M'.abs
