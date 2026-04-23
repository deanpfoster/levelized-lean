import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.DA.ToNA
import CslibHeaders.Computability.Proofs.Automata.DA.ToNA

/-! # Translation of DA into NA

  DA is a special case of NA (standard DFA-to-NFA embedding).

  Vocabulary:
    DA.toNA              -- embed a DA as an NA
    DA.FinAcc.toNAFinAcc -- embed a DA.FinAcc as an NA.FinAcc
    DA.Buchi.toNABuchi   -- embed a DA.Buchi as an NA.Buchi

  Theorems:
    toNA_run                -- a.toNA.Run xs ss ↔ a.run xs = ss
    toNAFinAcc_language_eq  -- language a.toNAFinAcc = language a
    toNABuchi_language_eq   -- language a.toNABuchi = language a
-/

open Cslib.Automata Cslib.Automata.DA

ProvenTheorem toNA_run :
  ∀ {State : Type u_1} {Symbol : Type u_2}
    {a : Cslib.Automata.DA State Symbol}
    {xs : Cslib.ωSequence Symbol} {ss : Cslib.ωSequence State},
    a.toNA.Run xs ss ↔ a.run xs = ss

ProvenTheorem toNAFinAcc_language_eq :
  ∀ {State : Type u_1} {Symbol : Type u_2}
    {a : Cslib.Automata.DA.FinAcc State Symbol},
    Acceptor.language a.toNAFinAcc = Acceptor.language a

ProvenTheorem toNABuchi_language_eq :
  ∀ {State : Type u_1} {Symbol : Type u_2}
    {a : Cslib.Automata.DA.Buchi State Symbol},
    ωAcceptor.language a.toNABuchi = ωAcceptor.language a
