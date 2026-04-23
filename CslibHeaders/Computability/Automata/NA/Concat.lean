import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Concat
import CslibHeaders.Computability.Proofs.Automata.NA.Concat

/-! # Concatenation of Nondeterministic Automata

  Vocabulary:
    concat          -- concatenation of an NA.FinAcc and an NA
    FinAcc.finConcat -- concatenation of two NA.FinAcc (totalized)

  Theorems:
    concat_run_proj        -- a run with a right state decomposes
    concat_run_exists      -- an accepting finite run + an infinite run combine
    concat_language_eq     -- Buchi language of concat = language na1 * language na2
    finConcat_language_eq  -- finConcat language = language na1 * language na2
-/

open Cslib.Automata.NA Cslib.Automata

ProvenTheorem concat_run_proj :
  ∀ {Symbol : Type u_1} {State1 : Type u_2} {State2 : Type u_3}
    {na1 : Cslib.Automata.NA.FinAcc State1 Symbol}
    {na2 : Cslib.Automata.NA State2 Symbol}
    {xs : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (State1 ⊕ State2)} {k : ℕ},
    (concat na1 na2).Run xs ss →
      (ss k).isRight = true →
        ∃ n, n ≤ k ∧
          Cslib.ωSequence.take n xs ∈ Acceptor.language na1 ∧
            ∃ ss2, na2.Run (Cslib.ωSequence.drop n xs) ss2 ∧
              Cslib.ωSequence.drop n ss = Cslib.ωSequence.map Sum.inr ss2

ProvenTheorem concat_run_exists :
  ∀ {Symbol : Type u_1} {State1 : Type u_2} {State2 : Type u_3}
    {na1 : Cslib.Automata.NA.FinAcc State1 Symbol}
    {na2 : Cslib.Automata.NA State2 Symbol}
    {xs1 : List Symbol} {xs2 : Cslib.ωSequence Symbol}
    {ss2 : Cslib.ωSequence State2},
    xs1 ∈ Acceptor.language na1 →
      na2.Run xs2 ss2 →
        ∃ ss, (concat na1 na2).Run (xs1 ++ω xs2) ss ∧
          Cslib.ωSequence.drop xs1.length ss = Cslib.ωSequence.map Sum.inr ss2

ProvenTheorem concat_language_eq :
  ∀ {Symbol : Type u_1} {State1 : Type u_2} {State2 : Type u_3}
    {na1 : Cslib.Automata.NA.FinAcc State1 Symbol}
    {na2 : Cslib.Automata.NA State2 Symbol}
    {acc2 : Set State2},
    ωAcceptor.language (NA.Buchi.mk (concat na1 na2) (Sum.inr '' acc2)) =
      Acceptor.language na1 * ωAcceptor.language (NA.Buchi.mk na2 acc2)

ProvenTheorem finConcat_language_eq :
  ∀ {Symbol : Type u_1} {State1 : Type u_2} {State2 : Type u_3}
    {na1 : Cslib.Automata.NA.FinAcc State1 Symbol}
    {na2 : Cslib.Automata.NA.FinAcc State2 Symbol}
    [_inst : Inhabited Symbol],
    Acceptor.language (NA.FinAcc.mk (na1.finConcat na2) (Sum.inr '' (Sum.inl '' na2.accept))) =
      Acceptor.language na1 * Acceptor.language na2
