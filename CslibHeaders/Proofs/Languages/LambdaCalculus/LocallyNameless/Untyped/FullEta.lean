import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

open Cslib Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

-- Bridge: original names -> _proof naming convention

noncomputable def FullEta.redex_app_l_cong_proof := @FullEta.redex_app_l_cong
noncomputable def FullEta.redex_app_r_cong_proof := @FullEta.redex_app_r_cong
noncomputable def FullEta.redex_abs_cong_proof := @FullEta.redex_abs_cong
