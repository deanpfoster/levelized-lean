import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Languages.OmegaRegularLanguage
import CslibHeaders.Computability.Proofs.Languages.OmegaRegularLanguage

/-! # ω-Regular Languages

  An ω-language is ω-regular iff accepted by a finite-state nondeterministic Buchi automaton.

  Vocabulary:
    ωLanguage.IsRegular -- predicate for ω-regular languages

  Theorems:
    ωreg_of_da_buchi   -- DA Buchi language is ω-regular
    ωreg_not_da_buchi   -- there exists an ω-regular language not accepted by any DA Buchi
    ωreg_regular_omegaLim -- ω-limit of a regular language is ω-regular
    ωreg_bot            -- ⊥ is ω-regular
    ωreg_top            -- ⊤ is ω-regular
    ωreg_sup            -- union of two ω-regular languages is ω-regular
    ωreg_inf            -- intersection of two ω-regular languages is ω-regular
    ωreg_iSup           -- finite union of ω-regular languages is ω-regular
    ωreg_iInf           -- finite intersection of ω-regular languages is ω-regular
    ωreg_hmul           -- regular * ω-regular is ω-regular
    ωreg_omegaPow       -- ω-power of regular is ω-regular
    ωreg_compl          -- complement of ω-regular is ω-regular
    ωreg_eq_fin_iSup_hmul_omegaPow -- characterisation as finite union of L * M^ω
-/

open Cslib.ωLanguage

ProvenTheorem ωreg_of_da_buchi :
  ∀ {Symbol : Type u_1} {State : Type} [Finite State]
    (da : Cslib.Automata.DA.Buchi State Symbol),
    (Cslib.Automata.ωAcceptor.language da).IsRegular

ProvenTheorem ωreg_not_da_buchi :
  ∃ (Symbol : Type) (p : Cslib.ωLanguage Symbol), p.IsRegular ∧
    ¬∃ (State : Type) (da : Cslib.Automata.DA.Buchi State Symbol),
      Cslib.Automata.ωAcceptor.language da = p

ProvenTheorem ωreg_regular_omegaLim :
  ∀ {Symbol : Type u_1} {l : Language Symbol},
    l.IsRegular → l↗ω.IsRegular

ProvenTheorem ωreg_bot :
  ∀ {Symbol : Type u_1}, (⊥ : Cslib.ωLanguage Symbol).IsRegular

ProvenTheorem ωreg_top :
  ∀ {Symbol : Type u_1}, (⊤ : Cslib.ωLanguage Symbol).IsRegular

ProvenTheorem ωreg_sup :
  ∀ {Symbol : Type u_1} {p1 p2 : Cslib.ωLanguage Symbol},
    p1.IsRegular → p2.IsRegular → (p1 ⊔ p2).IsRegular

ProvenTheorem ωreg_inf :
  ∀ {Symbol : Type u_1} {p1 p2 : Cslib.ωLanguage Symbol},
    p1.IsRegular → p2.IsRegular → (p1 ⊓ p2).IsRegular

ProvenTheorem ωreg_iSup :
  ∀ {Symbol : Type u_1} {I : Type u_2} [Finite I]
    {s : Set I} {p : I → Cslib.ωLanguage Symbol},
    (∀ i ∈ s, (p i).IsRegular) → (⨆ i ∈ s, p i).IsRegular

ProvenTheorem ωreg_iInf :
  ∀ {Symbol : Type u_1} {I : Type u_2} [Finite I]
    {s : Set I} {p : I → Cslib.ωLanguage Symbol},
    (∀ i ∈ s, (p i).IsRegular) → (⨅ i ∈ s, p i).IsRegular

ProvenTheorem ωreg_hmul :
  ∀ {Symbol : Type u_1} {l : Language Symbol}
    {p : Cslib.ωLanguage Symbol},
    l.IsRegular → p.IsRegular → (l * p).IsRegular

ProvenTheorem ωreg_omegaPow :
  ∀ {Symbol : Type u_1} [_inst : Inhabited Symbol]
    {l : Language Symbol},
    l.IsRegular → l^ω.IsRegular

ProvenTheorem ωreg_compl :
  ∀ {Symbol : Type} [_inst : Inhabited Symbol]
    {p : Cslib.ωLanguage Symbol},
    p.IsRegular → pᶜ.IsRegular

ProvenTheorem ωreg_eq_fin_iSup_hmul_omegaPow :
  ∀ {Symbol : Type u_1} [_inst : Inhabited Symbol]
    (p : Cslib.ωLanguage Symbol),
    p.IsRegular ↔ ∃ (n : ℕ) (l m : Fin n → Language Symbol),
      (∀ (i : Fin n), (l i).IsRegular ∧ (m i).IsRegular) ∧
      p = ⨆ i, l i * (m i)^ω
