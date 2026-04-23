/-! # Proofs: Perfect Secrecy

  Bridge to CSLib proofs. When CSLib is replaced with standalone
  definitions, these become real proofs instead of forwarding.
-/

import Cslib.Crypto.Protocols.PerfectSecrecy.Basic

open Cslib.Crypto.Protocols.PerfectSecrecy

-- Bridge: _proof names point to CSLib's theorems
noncomputable def perfectlySecret_iff_ciphertextIndist_proof :=
  @EncScheme.perfectlySecret_iff_ciphertextIndist

noncomputable def perfectlySecret_keySpace_ge_proof :=
  @EncScheme.perfectlySecret_keySpace_ge
