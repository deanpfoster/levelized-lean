import CslibHeaders.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic

/-! # Vocabulary for System F-sub -/

open Cslib Cslib.LambdaCalculus.LocallyNameless.Fsub

Vocabulary Ty := @Ty
Vocabulary Term := @Term
Vocabulary Binding := @Binding
Vocabulary Env := @Env
Vocabulary Ty.fv := @Ty.fv
Vocabulary Term.fv_ty := @Term.fv_ty
Vocabulary Term.fv_tm := @Term.fv_tm
