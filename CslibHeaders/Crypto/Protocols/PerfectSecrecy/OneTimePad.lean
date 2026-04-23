import CslibHeaders.Basic
import CslibHeaders.Defs.Crypto.Protocols.PerfectSecrecy.OneTimePad
import CslibHeaders.Proofs.Crypto.Protocols.PerfectSecrecy.OneTimePad

/-! # One-Time Pad — verified perfect secrecy

  Vocabulary (see Defs/):
    otp l — one-time pad encryption scheme over l-bit strings
    EncScheme.PerfectlySecret — posterior equals prior for all ciphertexts

  Read this file for WHAT is true.
  Read Defs/ for WHAT the words mean.
  Never need to open Code or Proofs.
-/

open Cslib.Crypto.Protocols.PerfectSecrecy

-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10)
ProvenTheorem otp_perfectlySecret :
  ∀ (l : ℕ), (otp l).PerfectlySecret
