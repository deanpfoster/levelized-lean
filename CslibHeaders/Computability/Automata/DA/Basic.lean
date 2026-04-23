import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.DA.Basic
import CslibHeaders.Computability.Proofs.Automata.DA.Basic

/-! # Deterministic Automata

  Vocabulary:
    DA       -- deterministic automaton (transition function + initial state)
    DA.run   -- infinite run of a DA on an ω-sequence
    DA.FinAcc -- DA with finite-string acceptance (DFA generalisation)
    DA.Buchi  -- deterministic Buchi automaton
    DA.Muller -- deterministic Muller automaton

  Theorems:
    run_zero           -- da.run xs 0 = da.start
    run_succ           -- da.run xs (n+1) = da.tr (da.run xs n) (xs n)
    mtr_extract_eq_run -- da.mtr da.start (xs.extract 0 n) = da.run xs n
-/

open Cslib.Automata.DA

ProvenTheorem run_zero :
  ∀ {State : Type u_1} {Symbol : Type u_2} {da : Cslib.Automata.DA State Symbol}
    {xs : Cslib.ωSequence Symbol},
    (da.run xs) 0 = da.start

ProvenTheorem run_succ :
  ∀ {State : Type u_1} {Symbol : Type u_2} {da : Cslib.Automata.DA State Symbol}
    {xs : Cslib.ωSequence Symbol} {n : ℕ},
    (da.run xs) (n + 1) = da.tr ((da.run xs) n) (xs n)

ProvenTheorem mtr_extract_eq_run :
  ∀ {State : Type u_1} {Symbol : Type u_2} {da : Cslib.Automata.DA State Symbol}
    {xs : Cslib.ωSequence Symbol} {n : ℕ},
    da.mtr da.start (xs.extract 0 n) = (da.run xs) n
