import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Pair
import CslibHeaders.Computability.Proofs.Automata.NA.Pair

/-! # Languages Determined by Pairs of States

  Vocabulary:
    LTS.pairLang    -- language of words taking LTS from state s to state t
    LTS.pairViaLang -- language of words going s to t via a state in a given set

  Theorems:
    mem_pairLang      -- xs ∈ lts.pairLang s t ↔ lts.MTr s xs t
    pairLang_regular  -- pairLang is regular for finite-state LTS
    mem_pairViaLang   -- membership characterisation for pairViaLang
    pairViaLang_regular -- pairViaLang is regular for finite-state LTS
    pairLang_append   -- pairLang closed under append
    pairLang_split    -- pairLang splits at intermediate states
    language_eq_fin_iSup_hmul_omegaPow -- finite-state NBA language = finite union of L * M^ω
-/

open Cslib Cslib.Automata

ProvenTheorem mem_pairLang :
  ∀ {Symbol : Type u_1} {State : Type}
    {lts : LTS State Symbol} {s t : State} {xs : List Symbol},
    xs ∈ lts.pairLang s t ↔ lts.MTr s xs t

ProvenTheorem pairLang_regular :
  ∀ {Symbol : Type u_1} {State : Type} [Finite State]
    {lts : LTS State Symbol} {s t : State},
    (lts.pairLang s t).IsRegular

ProvenTheorem mem_pairViaLang :
  ∀ {Symbol : Type u_1} {State : Type}
    {lts : LTS State Symbol} {via : Set State}
    {s t : State} {xs : List Symbol},
    xs ∈ lts.pairViaLang via s t ↔
      ∃ r ∈ via, ∃ xs1 xs2, lts.MTr s xs1 r ∧ lts.MTr r xs2 t ∧ xs1 ++ xs2 = xs

ProvenTheorem pairViaLang_regular :
  ∀ {Symbol : Type u_1} {State : Type} [Inhabited Symbol] [Finite State]
    {lts : LTS State Symbol} {via : Set State} {s t : State},
    (lts.pairViaLang via s t).IsRegular

ProvenTheorem pairLang_append :
  ∀ {Symbol : Type u_1} {State : Type}
    {lts : LTS State Symbol} {s0 s1 s2 : State}
    {xs1 xs2 : List Symbol},
    xs1 ∈ lts.pairLang s0 s1 → xs2 ∈ lts.pairLang s1 s2 →
      xs1 ++ xs2 ∈ lts.pairLang s0 s2

ProvenTheorem pairLang_split :
  ∀ {Symbol : Type u_1} {State : Type}
    {lts : LTS State Symbol} {s0 s2 : State}
    {xs1 xs2 : List Symbol},
    xs1 ++ xs2 ∈ lts.pairLang s0 s2 →
      ∃ s1, xs1 ∈ lts.pairLang s0 s1 ∧ xs2 ∈ lts.pairLang s1 s2

ProvenTheorem language_eq_fin_iSup_hmul_omegaPow :
  ∀ {Symbol : Type u_1} {State : Type} [_inst : Inhabited Symbol] [Finite State]
    (na : NA.Buchi State Symbol),
    ωAcceptor.language na =
      ⨆ s ∈ na.start, ⨆ t ∈ na.accept,
        na.pairLang s t * (na.pairLang t t)^ω
