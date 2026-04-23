import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.Named.Untyped.Basic
import CslibHeaders.Proofs.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Named Untyped Lambda Calculus

  Vocabulary:
    Term        -- lambda terms with named variables
    Context     -- one-hole contexts
    AlphaEquiv  -- alpha-equivalence (=alpha)

  Main result: contexts are complete — every term can be obtained
  by filling a context with a variable.
-/

open Cslib Cslib.LambdaCalculus.Named

ProvenTheorem Context.complete :
  ∀ {Var : Type u_1} (m : Term Var),
    ∃ (c : Context Var) (x : Var), m = c.fill (Term.var x)
