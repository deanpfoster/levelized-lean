import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.ToDA
import CslibHeaders.Computability.Proofs.Automata.NA.ToDA

/-! # Subset Construction: NA to DA

  The standard subset (powerset) construction translating NAs to DAs.

  Vocabulary:
    NA.FinAcc.toDAFinAcc -- subset construction

  Theorems:
    toDAFinAcc_language_eq -- language na.toDAFinAcc = language na
-/

open Cslib.Automata Cslib.Automata.NA.FinAcc

ProvenTheorem toDAFinAcc_language_eq :
  ∀ {State : Type u_1} {Symbol : Type u_2}
    {na : Cslib.Automata.NA.FinAcc State Symbol},
    Acceptor.language na.toDAFinAcc = Acceptor.language na
