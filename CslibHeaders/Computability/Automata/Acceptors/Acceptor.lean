import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.Acceptors.Acceptor
import CslibHeaders.Computability.Proofs.Automata.Acceptors.Acceptor

/-! # Acceptor -- Machines that recognise finite strings

  Vocabulary:
    Acceptor        -- typeclass for machines accepting finite strings
    Acceptor.language -- the language (set of accepted strings) of an acceptor

  Theorems:
    mem_language -- xs ∈ language a ↔ Accepts a xs
-/

open Cslib.Automata.Acceptor

ProvenTheorem mem_language :
  ∀ {Symbol : Type u_1} {A : Type u_2} [_inst : Cslib.Automata.Acceptor A Symbol]
    (a : A) (xs : List Symbol),
    xs ∈ language a ↔ Cslib.Automata.Acceptor.Accepts a xs
