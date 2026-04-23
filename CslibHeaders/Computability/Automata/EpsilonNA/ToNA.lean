import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.EpsilonNA.ToNA
import CslibHeaders.Computability.Proofs.Automata.EpsilonNA.ToNA

/-! # Translation of εNA into NA

  Vocabulary:
    εNA.FinAcc.toNAFinAcc -- convert an εNA.FinAcc into an NA.FinAcc (removing ε-transitions)

  Theorems:
    εNA_toNAFinAcc_language_eq -- language ena.toNAFinAcc = language ena
-/

open Cslib.Automata Cslib.Automata.εNA.FinAcc

ProvenTheorem εNA_toNAFinAcc_language_eq :
  ∀ {State : Type u_1} {Symbol : Type u_2}
    {ena : Cslib.Automata.εNA.FinAcc State Symbol},
    Acceptor.language ena.toNAFinAcc = Acceptor.language ena
