import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.Acceptors.OmegaAcceptor
import CslibHeaders.Computability.Proofs.Automata.Acceptors.OmegaAcceptor

/-! # OmegaAcceptor -- Machines that recognise infinite sequences

  Vocabulary:
    ωAcceptor          -- typeclass for machines accepting ω-sequences
    ωAcceptor.language -- the ω-language of an ω-acceptor

  Theorems:
    mem_language_ω -- xs ∈ language a ↔ Accepts a xs
-/

open Cslib.Automata.ωAcceptor

ProvenTheorem mem_language_ω :
  ∀ {Symbol : Type u_1} {A : Type u_2} [_inst : Cslib.Automata.ωAcceptor A Symbol]
    (a : A) (xs : Cslib.ωSequence Symbol),
    xs ∈ language a ↔ Cslib.Automata.ωAcceptor.Accepts a xs
