import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence

/-! # Beta-Eta Confluence for the Lambda Calculus

  Vocabulary:
    FullBetaEta -- combined beta-eta reduction (FullBeta | FullEta)

  Beta-eta reduction is confluent, following Nipkow's method of
  joining two individually confluent, strongly commuting reductions.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Term

-- Combined beta-eta reduction is confluent
ProvenTheorem confluent_beta_eta :
  ∀ {Var : Type u_1} [HasFresh Var] [DecidableEq Var],
    Relation.Confluent (@FullBetaEta Var)
