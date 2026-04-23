import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.BuchiInter
import CslibHeaders.Computability.Proofs.Automata.NA.BuchiInter

/-! # Intersection of Nondeterministic Buchi Automata

  The intersection automaton uses a history state to alternate between
  waiting for each component's accepting condition.

  Vocabulary:
    interNA     -- the intersection automaton
    interAccept -- the accepting condition of the intersection automaton

  Theorems:
    inter_language_eq -- language of intersection = intersection of languages
-/

open Cslib.Automata.NA.Buchi Cslib.Automata

ProvenTheorem inter_language_eq :
  ∀ {Symbol : Type u_1} {State : Bool → Type u_2}
    {na : (i : Bool) → Cslib.Automata.NA (State i) Symbol}
    {acc : (i : Bool) → Set (State i)},
    ωAcceptor.language (NA.Buchi.mk (interNA na acc) (interAccept acc)) =
      ⨅ i, ωAcceptor.language (NA.Buchi.mk (na i) (acc i))
