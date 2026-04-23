import DeanLean.Basic
import Crypto.Defs.OneTimePad
import Crypto.Defs.PerfectSecrecy
import Crypto.Proofs.OneTimePad

/-! # One-Time Pad (Katz-Lindell Construction 2.9)

  Vocabulary (see Defs/OneTimePad.lean):
    otp l — the one-time pad over l-bit strings (BitVec l)
           encryption and decryption are XOR
-/

open Cslib.Crypto.Protocols.PerfectSecrecy

-- The OTP is perfectly secret (Theorem 2.10)
ProvenTheorem otp_perfectlySecret :
    ∀ (l : ℕ), (otp l).PerfectlySecret
