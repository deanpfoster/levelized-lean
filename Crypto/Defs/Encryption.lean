/-! # Vocabulary: Private-Key Encryption Schemes

  Re-exports from CSLib. If CSLib is replaced, define these standalone.
  The header and proofs don't change.
-/

import Cslib.Crypto.Protocols.PerfectSecrecy.Encryption

namespace Crypto

-- The core structure
export Cslib.Crypto.Protocols.PerfectSecrecy (EncScheme)

end Crypto
