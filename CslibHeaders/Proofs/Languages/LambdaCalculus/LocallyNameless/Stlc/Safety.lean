import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Safety

open Cslib Cslib.LambdaCalculus.LocallyNameless

-- Bridge: original names -> _proof naming convention

noncomputable def Stlc.FullBeta.preservation_proof := @Stlc.FullBeta.preservation
noncomputable def Stlc.FullBeta.progress_proof := @Stlc.FullBeta.progress
