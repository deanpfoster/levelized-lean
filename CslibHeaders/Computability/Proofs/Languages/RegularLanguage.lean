import Cslib.Computability.Languages.RegularLanguage

open Cslib.Language

noncomputable def reg_iff_dfa_proof := @IsRegular.iff_dfa
noncomputable def reg_iff_nfa_proof := @IsRegular.iff_nfa
noncomputable def reg_compl_proof := @IsRegular.compl
noncomputable def reg_zero_proof := @IsRegular.zero
noncomputable def reg_one_proof := @IsRegular.one
noncomputable def reg_top_proof := @IsRegular.top
noncomputable def reg_inf_proof := @IsRegular.inf
noncomputable def reg_add_proof := @IsRegular.add
noncomputable def reg_iInf_proof := @IsRegular.iInf
noncomputable def reg_iSup_proof := @IsRegular.iSup
noncomputable def reg_mul_proof := @Cslib.Language.IsRegular.mul
noncomputable def reg_kstar_proof := @IsRegular.kstar
noncomputable def reg_congr_fin_index_proof := @IsRegular.congr_fin_index
