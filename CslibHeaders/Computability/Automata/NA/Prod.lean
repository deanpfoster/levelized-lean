import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Prod
import CslibHeaders.Computability.Proofs.Automata.NA.Prod

/-! # Product of Nondeterministic Automata

  Vocabulary:
    NA.iProd -- indexed product of NAs

  Theorems:
    iProd_run_iff -- (iProd na).Run xs ss ↔ ∀ i, (na i).Run xs (ss.map (· i))
-/

open Cslib.Automata.NA

ProvenTheorem iProd_run_iff :
  ∀ {Symbol : Type u_1} {I : Type u_2} {State : I → Type u_3}
    {na : (i : I) → Cslib.Automata.NA (State i) Symbol}
    {xs : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence ((i : I) → State i)},
    (iProd na).Run xs ss ↔
      ∀ (i : I), (na i).Run xs (Cslib.ωSequence.map (fun x => x i) ss)
