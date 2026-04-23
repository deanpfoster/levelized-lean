import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Total
import CslibHeaders.Computability.Proofs.Automata.NA.Total

/-! # Making a Nondeterministic Automaton Total

  Vocabulary:
    totalize -- make an NA total by adding a sink state

  Theorems:
    totalize_run_mtr     -- while in non-sink states, corresponds to original NA
    totalize_mtr_run     -- any finite execution extends to an infinite one
    totalize_language_eq -- totalize preserves the language
-/

open Cslib.Automata.NA Cslib.Automata

ProvenTheorem totalize_run_mtr :
  ∀ {Symbol : Type u_1} {State : Type u_2}
    {na : Cslib.Automata.NA State Symbol}
    {xs : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (State ⊕ Unit)} {n : ℕ},
    na.totalize.Run xs ss →
      (ss n).isLeft = true →
        ∃ s t, na.MTr s (Cslib.ωSequence.take n xs) t ∧
          s ∈ na.start ∧ ss 0 = Sum.inl s ∧ ss n = Sum.inl t

ProvenTheorem totalize_mtr_run :
  ∀ {Symbol : Type u_1} {State : Type u_2}
    {na : Cslib.Automata.NA State Symbol} [Inhabited Symbol]
    {xl : List Symbol} {s t : State},
    s ∈ na.start → na.MTr s xl t →
      ∃ xs ss, na.totalize.Run (xl ++ω xs) ss ∧
        ss 0 = Sum.inl s ∧ ss xl.length = Sum.inl t

ProvenTheorem totalize_language_eq :
  ∀ {Symbol : Type u_1} {State : Type u_2}
    {na : Cslib.Automata.NA.FinAcc State Symbol},
    Acceptor.language (NA.FinAcc.mk na.totalize (Sum.inl '' na.accept)) =
      Acceptor.language na
