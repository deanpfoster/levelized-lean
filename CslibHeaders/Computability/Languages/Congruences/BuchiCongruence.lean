import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Languages.Congruences.BuchiCongruence
import CslibHeaders.Computability.Proofs.Languages.Congruences.BuchiCongruence

/-! # Buchi Congruence

  A special right congruence used to prove closure of ω-regular languages
  under complementation.

  Vocabulary:
    BuchiCongruence -- the Buchi congruence of an NBA
    buchiFamily     -- the saturating family of ω-languages

  Theorems:
    buchiCongruence_fin_index -- BuchiCongruence has finite index for finite-state NBAs
    buchiFamily_cover         -- buchiFamily covers all ω-sequences
    buchiFamily_saturation    -- buchiFamily saturates the NBA language
-/

open Cslib.Automata.NA.Buchi Cslib.Automata

ProvenTheorem buchiCongruence_fin_index :
  ∀ {Symbol : Type u_1} {State : Type}
    {na : Cslib.Automata.NA.Buchi State Symbol} [Finite State],
    Finite (Quotient na.BuchiCongruence.eq)

ProvenTheorem buchiFamily_cover :
  ∀ {Symbol : Type u_1} {State : Type}
    {na : Cslib.Automata.NA.Buchi State Symbol}
    [_inst : Inhabited Symbol] [Finite State],
    ⨆ i, na.buchiFamily i = ⊤

ProvenTheorem buchiFamily_saturation :
  ∀ {Symbol : Type u_1} {State : Type}
    {na : Cslib.Automata.NA.Buchi State Symbol}
    [_inst : Inhabited Symbol],
    Set.Saturates (fun i => (na.buchiFamily i).toSet)
      (ωAcceptor.language na).toSet
