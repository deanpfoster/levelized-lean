import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

-- Bridge: original names -> _proof naming convention

noncomputable def subst_fresh_proof := @subst_fresh
noncomputable def subst_open_var_proof := @subst_open_var
noncomputable def subst_lc_proof := @subst_lc
noncomputable def beta_lc_proof := @beta_lc
