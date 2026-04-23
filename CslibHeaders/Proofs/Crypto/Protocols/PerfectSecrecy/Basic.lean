import Cslib.Crypto.Protocols.PerfectSecrecy.Basic

open Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

-- Bridge: CSLib theorems -> _proof naming convention
noncomputable def perfectlySecret_iff_ciphertextIndist_proof :=
  @perfectlySecret_iff_ciphertextIndist
noncomputable def perfectlySecret_keySpace_ge_proof := @perfectlySecret_keySpace_ge
