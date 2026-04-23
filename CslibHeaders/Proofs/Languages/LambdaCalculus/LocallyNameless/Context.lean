import Cslib.Languages.LambdaCalculus.LocallyNameless.Context

open Cslib Cslib.LambdaCalculus.LocallyNameless

-- Bridge: original names -> _proof naming convention

noncomputable def Context.map_val_keys_proof := @Context.map_val_keys
noncomputable def Context.map_val_mem_proof := @Context.map_val_mem
