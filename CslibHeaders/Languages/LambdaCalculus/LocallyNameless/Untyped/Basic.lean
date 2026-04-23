import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

/-! # Locally Nameless Untyped Lambda Calculus — Syntax

  Vocabulary:
    Term       -- locally nameless lambda terms (bvar, fvar, abs, app)
    Term.LC    -- locally closed terms
    Term.Value -- values (irreducible terms)
    Term.fv    -- free variables
    open' (^)  -- variable opening of closest binding
    close (^*) -- variable closing of closest binding
    subst      -- substitution of a free variable

  This module defines the core syntax. Theorems live in Properties,
  Congruence, and the reduction modules.
-/
