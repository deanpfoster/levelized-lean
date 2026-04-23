import CslibHeaders.Basic
import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Vocabulary for Named Untyped Lambda Calculus -/

open Cslib Cslib.LambdaCalculus.Named

Vocabulary Term := @Term
Vocabulary Term.fv := @Term.fv
Vocabulary Term.bv := @Term.bv
Vocabulary Term.vars := @Term.vars
Vocabulary Term.Subst := @Term.Subst
Vocabulary Term.rename := @Term.rename
Vocabulary Term.subst := @Term.subst
Vocabulary Context := @Context
Vocabulary Context.fill := @Context.fill
Vocabulary Term.AlphaEquiv := @Term.AlphaEquiv
