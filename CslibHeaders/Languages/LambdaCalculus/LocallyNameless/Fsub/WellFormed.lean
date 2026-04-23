import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed

/-! # System F-sub — Well-Formedness

  Vocabulary:
    Ty.Wf  -- well-formed types (locally closed, all free vars in context)
    Env.Wf -- well-formed environments (no duplicate keys, well-formed types)

  Well-formedness is preserved under permutation, weakening, narrowing,
  strengthening, and substitution.
-/
