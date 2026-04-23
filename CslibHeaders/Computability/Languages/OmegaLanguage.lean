import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Languages.OmegaLanguage
import CslibHeaders.Computability.Proofs.Languages.OmegaLanguage

/-! # ω-Language

  Vocabulary:
    ωLanguage          -- sets of infinite sequences over an alphabet
    ωLanguage.omegaPow -- l^ω, concatenation of infinitely many copies
    ωLanguage.omegaLim -- l↗ω, sequences with infinitely many prefixes in l
    ωLanguage.map      -- transform ω-language by mapping through a function

  Set algebra:
    ω_mem_top     -- s ∈ ⊤
    ω_notMem_bot  -- s ∉ ⊥
    ω_mem_sup     -- s ∈ p ⊔ q ↔ s ∈ p ∨ s ∈ q
    ω_mem_inf     -- s ∈ p ⊓ q ↔ s ∈ p ∧ s ∈ q
    ω_mem_compl   -- s ∈ pᶜ ↔ s ∉ p

  Concatenation / ω-power:
    ω_mem_hmul       -- s ∈ l * p ↔ ∃ x ∈ l, ∃ t ∈ p, x ++ω t = s
    ω_mem_omegaPow   -- s ∈ l^ω ↔ ∃ xs, xs.flatten = s ∧ ∀ k, xs k ∈ l - 1
    ω_mem_omegaLim   -- s ∈ l↗ω ↔ (∃ᶠ m in atTop, s.extract 0 m ∈ l)
    ω_mul_hmul       -- (l * m) * p = l * (m * p)
    ω_zero_hmul      -- 0 * p = ⊥
    ω_hmul_bot       -- l * ⊥ = ⊥
    ω_one_hmul       -- 1 * p = p
    ω_hmul_sup       -- l * (p ⊔ q) = l * p ⊔ l * q
    ω_add_hmul       -- (l + m) * p = l * p ⊔ m * p
    ω_omegaPow_of_sub_one -- (l - 1)^ω = l^ω
    ω_omegaPow_of_le_one  -- l ≤ 1 → l^ω = ⊥
    ω_omegaPow_eq_empty   -- l^ω = ⊥ → l ≤ 1
    ω_omegaPow_coind      -- p ≤ (l - 1) * p → p ≤ l^ω
    ω_hmul_omegaPow_eq_omegaPow      -- l * l^ω = l^ω
    ω_kstar_omegaPow_eq_omegaPow     -- l* ^ω = l^ω
    ω_kstar_hmul_omegaPow_eq_omegaPow -- l* * l^ω = l^ω
    ω_map_id   -- map id p = p
    ω_map_map  -- map g (map f p) = map (g ∘ f) p
-/

open Cslib.ωLanguage

ProvenTheorem ω_mem_top :
  ∀ {α : Type u_1} (s : Cslib.ωSequence α), s ∈ (⊤ : Cslib.ωLanguage α)

ProvenTheorem ω_notMem_bot :
  ∀ {α : Type u_1} (s : Cslib.ωSequence α), s ∉ (⊥ : Cslib.ωLanguage α)

ProvenTheorem ω_mem_sup :
  ∀ {α : Type u_1} (p q : Cslib.ωLanguage α) (s : Cslib.ωSequence α),
    s ∈ p ⊔ q ↔ s ∈ p ∨ s ∈ q

ProvenTheorem ω_mem_inf :
  ∀ {α : Type u_1} (p q : Cslib.ωLanguage α) (s : Cslib.ωSequence α),
    s ∈ p ⊓ q ↔ s ∈ p ∧ s ∈ q

ProvenTheorem ω_mem_compl :
  ∀ {α : Type u_1} (p : Cslib.ωLanguage α) (s : Cslib.ωSequence α),
    s ∈ pᶜ ↔ s ∉ p

ProvenTheorem ω_mem_hmul :
  ∀ {α : Type u_1} {l : Language α} {p : Cslib.ωLanguage α}
    {s : Cslib.ωSequence α},
    s ∈ l * p ↔ ∃ x ∈ l, ∃ t ∈ p, x ++ω t = s

ProvenTheorem ω_mem_omegaPow :
  ∀ {α : Type u_1} {l : Language α} {s : Cslib.ωSequence α}
    [_inst : Inhabited α],
    s ∈ l^ω ↔ ∃ xs : Cslib.ωSequence (List α), xs.flatten = s ∧ ∀ (k : ℕ), xs k ∈ l - 1

ProvenTheorem ω_mem_omegaLim :
  ∀ {α : Type u_1} {l : Language α} {s : Cslib.ωSequence α},
    s ∈ l↗ω ↔ ∃ᶠ (m : ℕ) in Filter.atTop, s.extract 0 m ∈ l

ProvenTheorem ω_mul_hmul :
  ∀ {α : Type u_1} {l m : Language α} {p : Cslib.ωLanguage α},
    l * m * p = l * (m * p)

ProvenTheorem ω_zero_hmul :
  ∀ {α : Type u_1} {p : Cslib.ωLanguage α},
    (0 : Language α) * p = ⊥

ProvenTheorem ω_hmul_bot :
  ∀ {α : Type u_1} {l : Language α},
    l * (⊥ : Cslib.ωLanguage α) = ⊥

ProvenTheorem ω_one_hmul :
  ∀ {α : Type u_1} {p : Cslib.ωLanguage α},
    (1 : Language α) * p = p

ProvenTheorem ω_hmul_sup :
  ∀ {α : Type u_1} {l : Language α} {p q : Cslib.ωLanguage α},
    l * (p ⊔ q) = l * p ⊔ l * q

ProvenTheorem ω_add_hmul :
  ∀ {α : Type u_1} {l m : Language α} {p : Cslib.ωLanguage α},
    (l + m) * p = l * p ⊔ m * p

ProvenTheorem ω_omegaPow_of_sub_one :
  ∀ {α : Type u_1} {l : Language α} [_inst : Inhabited α],
    (l - 1)^ω = l^ω

ProvenTheorem ω_omegaPow_of_le_one :
  ∀ {α : Type u_1} {l : Language α} [_inst : Inhabited α],
    l ≤ 1 → l^ω = ⊥

ProvenTheorem ω_omegaPow_eq_empty :
  ∀ {α : Type u_1} {l : Language α} [_inst : Inhabited α],
    l^ω = ⊥ → l ≤ 1

ProvenTheorem ω_omegaPow_coind :
  ∀ {α : Type u_1} {l : Language α} {p : Cslib.ωLanguage α}
    [_inst : Inhabited α],
    p ≤ (l - 1) * p → p ≤ l^ω

ProvenTheorem ω_hmul_omegaPow_eq_omegaPow :
  ∀ {α : Type u_1} [_inst : Inhabited α] (l : Language α),
    l * l^ω = l^ω

ProvenTheorem ω_kstar_omegaPow_eq_omegaPow :
  ∀ {α : Type u_1} [_inst : Inhabited α] (l : Language α),
    (KStar.kstar l)^ω = l^ω

ProvenTheorem ω_kstar_hmul_omegaPow_eq_omegaPow :
  ∀ {α : Type u_1} [_inst : Inhabited α] (l : Language α),
    KStar.kstar l * l^ω = l^ω

ProvenTheorem ω_map_id :
  ∀ {α : Type u_1} (p : Cslib.ωLanguage α), map id p = p

ProvenTheorem ω_map_map :
  ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    (g : β → γ) (f : α → β) (p : Cslib.ωLanguage α),
    map g (map f p) = map (g ∘ f) p
