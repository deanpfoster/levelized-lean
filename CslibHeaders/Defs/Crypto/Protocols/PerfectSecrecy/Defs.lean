import CslibHeaders.Basic
import CslibHeaders.Defs.Crypto.Protocols.PerfectSecrecy.Encryption
import Cslib.Crypto.Protocols.PerfectSecrecy.Defs

/-! # Vocabulary for Perfect Secrecy Definitions -/

open Cslib.Crypto.Protocols.PerfectSecrecy
open Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

Vocabulary EncScheme.ciphertextDist := @EncScheme.ciphertextDist
Vocabulary EncScheme.jointDist := @EncScheme.jointDist
Vocabulary EncScheme.marginalCiphertextDist := @EncScheme.marginalCiphertextDist
Vocabulary EncScheme.posteriorMsgDist := @EncScheme.posteriorMsgDist
Vocabulary EncScheme.PerfectlySecret := @EncScheme.PerfectlySecret
Vocabulary EncScheme.CiphertextIndist := @EncScheme.CiphertextIndist
