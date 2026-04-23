import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype

open Cslib Cslib.LambdaCalculus.LocallyNameless.Fsub

-- Bridge: original names -> _proof naming convention

noncomputable def Sub.trans_proof := @Sub.trans
noncomputable def Sub.refl_proof := @Sub.refl
noncomputable def Sub.narrow_proof := @Sub.narrow
