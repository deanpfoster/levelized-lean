import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

/-! # LcAt: Alternative Definition of Local Closure

  Vocabulary:
    LcAt k M -- all bound indices of M are smaller than k

  When k = 0, LcAt is equivalent to LC.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped
open Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

-- LcAt 0 is equivalent to LC
ProvenTheorem lcAt_iff_LC :
  ∀ {Var : Type u_1} (M : LambdaCalculus.LocallyNameless.Untyped.Term Var)
    [inst : HasFresh Var],
    LcAt 0 M ↔ M.LC
