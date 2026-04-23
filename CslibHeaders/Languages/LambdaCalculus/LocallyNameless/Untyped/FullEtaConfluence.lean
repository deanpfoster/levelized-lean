import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEtaConfluence

/-! # Eta Confluence for the Lambda Calculus

  Eta reduction is strongly confluent, following Nipkow's proof.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Term

-- Eta reduction is strongly confluent
ProvenTheorem stronglyConfluent_eta :
  ∀ {Var : Type u_1} [HasFresh Var] [DecidableEq Var],
    Relation.StronglyConfluent (@FullEta Var)
