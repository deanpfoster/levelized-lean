import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Languages.Language
import CslibHeaders.Computability.Proofs.Languages.Language

/-! # Language (additional definitions and theorems)

  Additional theorems about `Language` beyond Mathlib.

  Theorems:
    mem_biInf          -- x ∈ ⨅ i ∈ s, l i ↔ ∀ i ∈ s, x ∈ l i
    mem_biSup          -- x ∈ ⨆ i ∈ s, l i ↔ ∃ i ∈ s, x ∈ l i
    le_one_iff_eq      -- l ≤ 1 ↔ l = 0 ∨ l = 1
    mem_sub_one        -- x ∈ (l - 1) ↔ x ∈ l ∧ x ≠ []
    reverse_sub        -- (l - m).reverse = l.reverse - m.reverse
    lang_sub_one_mul   -- (l - 1) * l = l * l - 1
    lang_mul_sub_one   -- l * (l - 1) = l * l - 1
    kstar_sub_one      -- l* - 1 = (l - 1) * l*
    sub_one_kstar      -- (l - 1)* = l*
    kstar_iff_mul_add  -- m = l* ↔ m = (l - 1) * m + 1
-/

open Language

ProvenTheorem mem_biInf :
  ∀ {α : Type u_1} {I : Type u_2} (s : Set I) (l : I → Language α) (x : List α),
    x ∈ ⨅ i ∈ s, l i ↔ ∀ i ∈ s, x ∈ l i

ProvenTheorem mem_biSup :
  ∀ {α : Type u_1} {I : Type u_2} (s : Set I) (l : I → Language α) (x : List α),
    x ∈ ⨆ i ∈ s, l i ↔ ∃ i ∈ s, x ∈ l i

ProvenTheorem le_one_iff_eq :
  ∀ {α : Type u_1} {l : Language α}, l ≤ 1 ↔ l = 0 ∨ l = 1

ProvenTheorem mem_sub_one :
  ∀ {α : Type u_1} {l : Language α} (x : List α), x ∈ l - 1 ↔ x ∈ l ∧ x ≠ []

ProvenTheorem reverse_sub :
  ∀ {α : Type u_1} (l m : Language α), (l - m).reverse = l.reverse - m.reverse

ProvenTheorem lang_sub_one_mul :
  ∀ {α : Type u_1} {l : Language α}, (l - 1) * l = l * l - 1

ProvenTheorem lang_mul_sub_one :
  ∀ {α : Type u_1} {l : Language α}, l * (l - 1) = l * l - 1

ProvenTheorem kstar_sub_one :
  ∀ {α : Type u_1} {l : Language α}, KStar.kstar l - 1 = (l - 1) * KStar.kstar l

ProvenTheorem sub_one_kstar :
  ∀ {α : Type u_1} {l : Language α}, KStar.kstar (l - 1) = KStar.kstar l

ProvenTheorem kstar_iff_mul_add :
  ∀ {α : Type u_1} {l m : Language α}, m = KStar.kstar l ↔ m = (l - 1) * m + 1
