import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence

/-! # Beta Confluence for the Lambda Calculus

  Vocabulary:
    Parallel -- parallel beta reduction

  The proof follows Tait and Martin-Lof's method:
  1. Define parallel reduction with single beta included in parallel included in multi-beta
  2. Show parallel reduction has the diamond property
  3. Lift to the Church-Rosser theorem for multi-step beta
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Term

-- Multi-step parallel reduction equals multi-step beta reduction
ProvenTheorem parachain_iff_redex :
  ∀ {Var : Type u_1} {M N : Term Var} [HasFresh Var] [DecidableEq Var],
    Relation.ReflTransGen Parallel M N ↔
    Relation.ReflTransGen FullBeta M N

-- Parallel reduction has the diamond property
ProvenTheorem para_diamond :
  ∀ {Var : Type u_1} [HasFresh Var] [DecidableEq Var],
    Relation.Diamond (@Parallel Var)

-- Parallel reduction is confluent
ProvenTheorem para_confluence :
  ∀ {Var : Type u_1} [HasFresh Var] [DecidableEq Var],
    Relation.Confluent (@Parallel Var)

-- Full beta reduction is confluent (Church-Rosser)
ProvenTheorem confluence_beta :
  ∀ {Var : Type u_1} [HasFresh Var] [DecidableEq Var],
    Relation.Confluent (@FullBeta Var)
