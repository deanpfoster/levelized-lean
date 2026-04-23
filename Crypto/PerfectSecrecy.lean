import DeanLean.Basic
import Crypto.Defs.PerfectSecrecy
import Crypto.Proofs.PerfectSecrecy

/-! # Perfect Secrecy (Katz-Lindell Chapter 2)

  Vocabulary (see Defs/PerfectSecrecy.lean):
    EncScheme M K C  — encryption scheme with Gen, Enc, Dec + correctness
    PerfectlySecret  — posterior = prior for all ciphertexts
    CiphertextIndist — ciphertext distribution independent of message
-/

open Cslib.Crypto.Protocols.PerfectSecrecy

-- Ciphertext indistinguishability ↔ perfect secrecy (Lemma 2.5)
ProvenTheorem perfectlySecret_iff_ciphertextIndist :
    ∀ {M K C : Type} (scheme : EncScheme M K C),
    scheme.PerfectlySecret ↔ scheme.CiphertextIndist

-- Shannon's theorem: |K| ≥ |M| (Theorem 2.12)
ProvenTheorem perfectlySecret_keySpace_ge :
    ∀ {M K C : Type} [Finite K] (scheme : EncScheme M K C),
    scheme.PerfectlySecret → Nat.card K ≥ Nat.card M
