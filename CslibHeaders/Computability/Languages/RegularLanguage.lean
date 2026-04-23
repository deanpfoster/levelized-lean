import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Languages.RegularLanguage
import CslibHeaders.Computability.Proofs.Languages.RegularLanguage

/-! # Regular Languages

  Closure properties of regular languages under boolean operations,
  concatenation, and Kleene star.

  Theorems:
    reg_iff_dfa  -- l.IsRegular ↔ ∃ State, Finite State, ∃ dfa, language dfa = l
    reg_iff_nfa  -- l.IsRegular ↔ ∃ State, Finite State, ∃ nfa, language nfa = l
    reg_compl    -- l.IsRegular → lᶜ.IsRegular
    reg_zero     -- (0 : Language).IsRegular
    reg_one      -- (1 : Language).IsRegular
    reg_top      -- ⊤.IsRegular
    reg_inf      -- l1.IsRegular → l2.IsRegular → (l1 ⊓ l2).IsRegular
    reg_add      -- l1.IsRegular → l2.IsRegular → (l1 + l2).IsRegular
    reg_iInf     -- finite intersection of regulars is regular
    reg_iSup     -- finite union of regulars is regular
    reg_mul      -- l1.IsRegular → l2.IsRegular → (l1 * l2).IsRegular
    reg_kstar    -- l.IsRegular → l*.IsRegular
    reg_congr_fin_index -- finite-index right congruence classes are regular
-/

open Cslib.Language

ProvenTheorem reg_iff_dfa :
  ∀ {Symbol : Type u_1} {l : Language Symbol},
    l.IsRegular ↔ ∃ State : Type, ∃ (_ : Finite State),
      ∃ dfa : Cslib.Automata.DA.FinAcc State Symbol,
        Cslib.Automata.Acceptor.language dfa = l

ProvenTheorem reg_iff_nfa :
  ∀ {Symbol : Type u_1} {l : Language Symbol},
    l.IsRegular ↔ ∃ State : Type, ∃ (_ : Finite State),
      ∃ nfa : Cslib.Automata.NA.FinAcc State Symbol,
        Cslib.Automata.Acceptor.language nfa = l

ProvenTheorem reg_compl :
  ∀ {Symbol : Type u_1} {l : Language Symbol},
    l.IsRegular → lᶜ.IsRegular

ProvenTheorem reg_zero :
  ∀ {Symbol : Type u_1}, Language.IsRegular (0 : Language Symbol)

ProvenTheorem reg_one :
  ∀ {Symbol : Type u_1}, Language.IsRegular (1 : Language Symbol)

ProvenTheorem reg_top :
  ∀ {Symbol : Type u_1}, (⊤ : Language Symbol).IsRegular

ProvenTheorem reg_inf :
  ∀ {Symbol : Type u_1} {l1 l2 : Language Symbol},
    l1.IsRegular → l2.IsRegular → (l1 ⊓ l2).IsRegular

ProvenTheorem reg_add :
  ∀ {Symbol : Type u_1} {l1 l2 : Language Symbol},
    l1.IsRegular → l2.IsRegular → (l1 + l2).IsRegular

ProvenTheorem reg_iInf :
  ∀ {Symbol : Type u_1} {I : Type u_2} [Finite I]
    {s : Set I} {l : I → Language Symbol},
    (∀ i ∈ s, (l i).IsRegular) → (⨅ i ∈ s, l i).IsRegular

ProvenTheorem reg_iSup :
  ∀ {Symbol : Type u_1} {I : Type u_2} [Finite I]
    {s : Set I} {l : I → Language Symbol},
    (∀ i ∈ s, (l i).IsRegular) → (⨆ i ∈ s, l i).IsRegular

ProvenTheorem reg_mul :
  ∀ {Symbol : Type u_1} [_inst : Inhabited Symbol]
    {l1 l2 : Language Symbol},
    l1.IsRegular → l2.IsRegular → (l1 * l2).IsRegular

ProvenTheorem reg_kstar :
  ∀ {Symbol : Type u_1} [_inst : Inhabited Symbol]
    {l : Language Symbol},
    l.IsRegular → (KStar.kstar l).IsRegular

ProvenTheorem reg_congr_fin_index :
  ∀ {Symbol : Type} [c : Cslib.RightCongruence Symbol]
    [Finite (Quotient c.eq)] (a : Quotient c.eq),
    (Cslib.RightCongruence.eqvCls a).IsRegular
