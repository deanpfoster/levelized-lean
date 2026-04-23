import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Languages.ExampleEventuallyZero
import CslibHeaders.Computability.Proofs.Languages.ExampleEventuallyZero

/-! # Example: Eventually Zero

  An ω-regular language that is not accepted by any deterministic Buchi automaton.

  Vocabulary:
    eventually_zero    -- the ω-language of sequences eventually equal to 0
    eventually_zero_na -- a 2-state NBA accepting eventually_zero

  Theorems:
    eventually_zero_accepted_by_na_buchi -- language eventually_zero_na = eventually_zero
    eventually_zero_not_omegaLim -- no language l has l↗ω = eventually_zero
-/

open Cslib.ωLanguage.Example Cslib.Automata

ProvenTheorem eventually_zero_accepted_by_na_buchi :
  ωAcceptor.language eventually_zero_na = eventually_zero

ProvenTheorem eventually_zero_not_omegaLim :
  ¬∃ l : Language (Fin 2), l↗ω = eventually_zero
