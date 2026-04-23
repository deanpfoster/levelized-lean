import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp

/-! # Multi-Application for Lambda Terms

  Vocabulary:
    multiApp f [x1,...,xn] -- left-associative application (((f x1) x2) ... xn)
    ListFullBeta           -- single beta step in a list of arguments

  Infrastructure for the strong normalization proof.
-/
