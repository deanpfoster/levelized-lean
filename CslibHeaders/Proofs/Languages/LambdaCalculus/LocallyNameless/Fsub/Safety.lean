import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Safety

open Cslib Cslib.LambdaCalculus.LocallyNameless.Fsub

-- Bridge: original names -> _proof naming convention

noncomputable def Typing.preservation_proof := @Typing.preservation
noncomputable def Typing.progress_proof := @Typing.progress
