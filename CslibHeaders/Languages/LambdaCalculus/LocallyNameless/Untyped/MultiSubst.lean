import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiSubst
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiSubst

/-! # Multi-Substitution for Lambda Terms

  Vocabulary:
    Env         -- an environment mapping variables to terms
    multiSubst  -- simultaneous substitution of all env bindings
    env_LC      -- all terms in an environment are locally closed

  Infrastructure for the strong normalization proof.
-/
