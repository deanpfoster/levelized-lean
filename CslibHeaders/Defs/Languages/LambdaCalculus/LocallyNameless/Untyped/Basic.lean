import CslibHeaders.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

/-! # Vocabulary for Locally Nameless Untyped Lambda Calculus -/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped

Vocabulary Term := @Term
Vocabulary Term.openRec := @Term.openRec
Vocabulary Term.open' := @Term.open'
Vocabulary Term.closeRec := @Term.closeRec
Vocabulary Term.close := @Term.close
Vocabulary Term.subst := @Term.subst
Vocabulary Term.fv := @Term.fv
Vocabulary Term.LC := @Term.LC
Vocabulary Term.Value := @Term.Value
