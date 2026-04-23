import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Sum
import CslibHeaders.Computability.Proofs.Automata.NA.Sum

/-! # Sum of Nondeterministic Automata

  Vocabulary:
    iSum -- indexed sum (disjoint union) of NAs

  Theorems:
    iSum_run_iff     -- a run of the sum is a run of one component
    iSum_language_eq -- language of Buchi sum = union of component languages
-/

open Cslib.Automata.NA Cslib.Automata

ProvenTheorem iSum_run_iff :
  ∀ {Symbol : Type u_1} {I : Type u_2} {State : I → Type u_3}
    {na : (i : I) → Cslib.Automata.NA (State i) Symbol}
    {xs : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence ((i : I) × State i)},
    (iSum na).Run xs ss ↔
      ∃ i ss_i, (na i).Run xs ss_i ∧
        Cslib.ωSequence.map (Sigma.mk i) ss_i = ss

ProvenTheorem iSum_language_eq :
  ∀ {Symbol : Type u_1} {I : Type u_2} {State : I → Type u_3}
    {na : (i : I) → Cslib.Automata.NA (State i) Symbol}
    {acc : (i : I) → Set (State i)},
    ωAcceptor.language (NA.Buchi.mk (iSum na) (⋃ i, Sigma.mk i '' acc i)) =
      ⨆ i, ωAcceptor.language (NA.Buchi.mk (na i) (acc i))
