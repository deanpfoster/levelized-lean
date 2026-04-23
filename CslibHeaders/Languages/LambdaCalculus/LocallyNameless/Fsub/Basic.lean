import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic

/-! # System F-sub — Syntax

  Vocabulary:
    Ty      -- types (top, bvar, fvar, arrow, all, sum)
    Term    -- terms (bvar, fvar, abs, app, tabs, tapp, let', inl, inr, case)
    Binding -- context bindings (sub for subtype, ty for type)
    Env     -- typing environment (Context Var (Binding Var))

  This module defines the core syntax of System F with subtyping.
-/
