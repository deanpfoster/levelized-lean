/-! # Vocabulary: Perfect Secrecy

  Re-exports from CSLib. The language for stating secrecy theorems.
-/

import Cslib.Crypto.Protocols.PerfectSecrecy.Defs

namespace Crypto

open Cslib.Crypto.Protocols.PerfectSecrecy

-- Definitions that appear in theorem types
export Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
  (ciphertextDist PerfectlySecret CiphertextIndist
   jointDist marginalCiphertextDist posteriorMsgDist)

end Crypto
