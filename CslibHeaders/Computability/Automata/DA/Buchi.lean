import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.DA.Buchi
import CslibHeaders.Computability.Proofs.Automata.DA.Buchi

/-! # Deterministic Buchi Automata

  The ω-language accepted by a deterministic Buchi automaton is the ω-limit
  of the language accepted by the same automaton viewed as a DFA.

  Theorems:
    buchi_eq_finAcc_omegaLim -- language (Buchi.mk da acc) = (language (FinAcc.mk da acc))↗ω
-/

open Cslib.Automata Cslib.Automata.DA

ProvenTheorem buchi_eq_finAcc_omegaLim :
  ∀ {State : Type u_1} {Symbol : Type u_2} {da : Cslib.Automata.DA State Symbol}
    {acc : Set State},
    ωAcceptor.language (DA.Buchi.mk da acc) =
      (Acceptor.language (DA.FinAcc.mk da acc))↗ω
