import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.BuchiEquiv
import CslibHeaders.Computability.Proofs.Automata.NA.BuchiEquiv

/-! # Equivalence of Nondeterministic Buchi Automata

  Vocabulary:
    NA.Buchi.reindex -- lift a state equivalence to an NBA equivalence

  Theorems:
    reindex_language_eq -- language (nba.reindex f) = language nba
-/

open Cslib.Automata.NA.Buchi Cslib.Automata

ProvenTheorem reindex_language_eq :
  ∀ {Symbol : Type u_1} {State : Type u_2} {State' : Type u_3}
    {f : State ≃ State'}
    {nba : Cslib.Automata.NA.Buchi State Symbol},
    ωAcceptor.language ((reindex f) nba) = ωAcceptor.language nba
