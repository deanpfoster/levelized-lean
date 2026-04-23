import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Hist
import CslibHeaders.Computability.Proofs.Automata.NA.Hist

/-! # Adding History States to a Nondeterministic Automaton

  Vocabulary:
    NA.addHist -- augment an NA with a history state

  Theorems:
    hist_run_proj   -- every run of the history automaton projects onto a run of the original
    hist_run_exists -- for every run of the original, there exists a history-augmented run
-/

open Cslib.Automata.NA

ProvenTheorem hist_run_proj :
  ∀ {Symbol : Type u_1} {State : Type u_2} {Hist : Type u_3}
    {na : Cslib.Automata.NA State Symbol}
    {start' : State → Hist} {tr' : State × Hist → Symbol → State → Hist}
    {xs : Cslib.ωSequence Symbol} {ss : Cslib.ωSequence (State × Hist)},
    (na.addHist start' tr').Run xs ss →
      na.Run xs (Cslib.ωSequence.map Prod.fst ss)

ProvenTheorem hist_run_exists :
  ∀ {Symbol : Type u_1} {State : Type u_2} {Hist : Type u_3}
    {na : Cslib.Automata.NA State Symbol}
    {start' : State → Hist} {tr' : State × Hist → Symbol → State → Hist}
    {xs : Cslib.ωSequence Symbol} {ss : Cslib.ωSequence State},
    na.Run xs ss →
      ∃ ss', (na.addHist start' tr').Run xs ss' ∧
        Cslib.ωSequence.map Prod.fst ss' = ss
