import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.DA.Congr
import CslibHeaders.Computability.Proofs.Automata.DA.Congr

/-! # Deterministic Automaton for a Right Congruence

  Every right congruence gives rise to a DA whose states are equivalence classes.

  Vocabulary:
    RightCongruence -- equivalence relation preserved by right-concatenation

  Theorems:
    congr_mtr_eq     -- c.toDA.mtr c.toDA.start xs = ⟦xs⟧
    congr_language_eq -- language (FinAcc.mk c.toDA {a}) = eqvCls a
-/

open Cslib Cslib.Automata

ProvenTheorem congr_mtr_eq :
  ∀ {Symbol : Type u_1} [c : RightCongruence Symbol] {xs : List Symbol},
    RightCongruence.toDA.mtr RightCongruence.toDA.start xs = ⟦xs⟧

ProvenTheorem congr_language_eq :
  ∀ {Symbol : Type u_1} [c : RightCongruence Symbol] {a : Quotient c.eq},
    Acceptor.language (DA.FinAcc.mk (RightCongruence.toDA (Symbol := Symbol)) {a}) =
      RightCongruence.eqvCls a
