import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

-- Bridge: original names -> _proof naming convention

noncomputable def FullBeta.redex_app_l_cong_proof := @FullBeta.redex_app_l_cong
noncomputable def FullBeta.redex_app_r_cong_proof := @FullBeta.redex_app_r_cong
noncomputable def FullBeta.redex_abs_cong_proof := @FullBeta.redex_abs_cong
