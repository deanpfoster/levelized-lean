import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing

/-! # System F-sub — Typing Relation

  Vocabulary:
    Typing -- the typing relation (Gamma |- t : tau)

  Typing supports weakening, narrowing, term substitution,
  and type substitution.
-/
