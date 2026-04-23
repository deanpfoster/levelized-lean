import CslibHeaders.Basic
import CslibHeaders.Defs.Crypto.Protocols.PerfectSecrecy.Defs
import CslibHeaders.Proofs.Crypto.Protocols.PerfectSecrecy.Basic

/-! # Perfect Secrecy — characterization theorems

  Vocabulary (see Defs/):
    EncScheme M K C         — private-key encryption scheme (Gen, Enc, Dec)
    EncScheme.PerfectlySecret — posterior equals prior for all ciphertexts
    EncScheme.CiphertextIndist — ciphertext distribution independent of message
    EncScheme.ciphertextDist — distribution of Enc_K(m) when K <- Gen

  Read this file for WHAT is true.
  Read Defs/ for WHAT the words mean.
  Never need to open Code or Proofs.
-/

open Cslib.Crypto.Protocols.PerfectSecrecy
open Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

-- Characterization: perfect secrecy iff ciphertext indistinguishability
-- ([KatzLindell2020], Lemma 2.5)
ProvenTheorem perfectlySecret_iff_ciphertextIndist :
  ∀ {M K C : Type u_1} (scheme : EncScheme M K C),
    scheme.PerfectlySecret ↔ scheme.CiphertextIndist

-- Shannon's theorem: perfect secrecy requires |K| >= |M|
-- ([KatzLindell2020], Theorem 2.12)
ProvenTheorem perfectlySecret_keySpace_ge :
  ∀ {M K C : Type u_1} [Finite K] (scheme : EncScheme M K C),
    scheme.PerfectlySecret → Nat.card K ≥ Nat.card M
