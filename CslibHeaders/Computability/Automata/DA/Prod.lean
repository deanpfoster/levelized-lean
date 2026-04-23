import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.DA.Prod
import CslibHeaders.Computability.Proofs.Automata.DA.Prod

/-! # Product of Deterministic Automata

  Vocabulary:
    DA.prod -- product of two DAs

  Theorems:
    prod_mtr_eq -- (da1.prod da2).mtr s xs = (da1.mtr s.1 xs, da2.mtr s.2 xs)
-/

open Cslib.Automata.DA

ProvenTheorem prod_mtr_eq :
  ∀ {State1 : Type u_1} {State2 : Type u_2} {Symbol : Type u_3}
    (da1 : Cslib.Automata.DA State1 Symbol) (da2 : Cslib.Automata.DA State2 Symbol)
    (s : State1 × State2) (xs : List Symbol),
    (da1.prod da2).mtr s xs = (da1.mtr s.1 xs, da2.mtr s.2 xs)
