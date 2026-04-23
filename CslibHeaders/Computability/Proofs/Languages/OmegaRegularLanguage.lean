import Cslib.Computability.Languages.OmegaRegularLanguage

open Cslib.ωLanguage

noncomputable def ωreg_of_da_buchi_proof := @IsRegular.of_da_buchi
noncomputable def ωreg_not_da_buchi_proof := @IsRegular.not_da_buchi
noncomputable def ωreg_regular_omegaLim_proof := @IsRegular.regular_omegaLim
noncomputable def ωreg_bot_proof := @IsRegular.bot
noncomputable def ωreg_top_proof := @IsRegular.top
noncomputable def ωreg_sup_proof := @IsRegular.sup
noncomputable def ωreg_inf_proof := @IsRegular.inf
noncomputable def ωreg_iSup_proof := @IsRegular.iSup
noncomputable def ωreg_iInf_proof := @IsRegular.iInf
noncomputable def ωreg_hmul_proof := @IsRegular.hmul
noncomputable def ωreg_omegaPow_proof := @IsRegular.omegaPow
noncomputable def ωreg_compl_proof := @IsRegular.compl
noncomputable def ωreg_eq_fin_iSup_hmul_omegaPow_proof := @IsRegular.eq_fin_iSup_hmul_omegaPow
