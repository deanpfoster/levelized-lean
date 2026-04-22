import DeanLean.Cpp.Defs.Algorithm
import DeanLean.Cpp.Proofs.Algorithm
import DeanLean.Cpp.Tests.Algorithm

/-! # C++ algorithms (N4950 §27.7-27.9)

  Formalizes basic C++ algorithms from `<algorithm>`:
  - `cppMin` / `cppMax` — min and max of two values (§27.8.5-6)
  - `cppClamp` — clamp a value to a range (§27.8.8)
  - `minElement` / `maxElement` — min/max of a list (§27.8.5-6)
  - `isSorted` — check if a list is sorted (§27.8.4)

  All operations use the `StrongOrd` typeclass with `strongCmp`.
  The `StrongOrd` typeclass provides the axioms needed for proofs:
  reflexivity, antisymmetry (via `flip`), and transitivity.
-/

namespace Cpp

variable {T : Type} [StrongOrd T]

/-! ## Vocabulary — definitions that appear in theorem types

  cmpLe a b := StrongOrd.strongCmp a b ≠ Ordering.gt
    (the ≤ relation derived from three-way comparison)

  class StrongOrdEq (T) [StrongOrd T] : Prop where
    cmp_eq_imp_eq : ∀ (a b : T), StrongOrd.strongCmp a b = .eq → a = b
    (comparison-equal implies actually equal — needed for min/max commutativity)
-/

/-! ## Signatures -/

Signature Cpp.cppMin : {T : Type} → [StrongOrd T] → T → T → T
Signature Cpp.cppMax : {T : Type} → [StrongOrd T] → T → T → T
Signature Cpp.cppClamp : {T : Type} → [StrongOrd T] → T → T → T → T
Signature Cpp.minElement : {T : Type} → [StrongOrd T] → [Inhabited T] → List T → T
Signature Cpp.maxElement : {T : Type} → [StrongOrd T] → [Inhabited T] → List T → T
Signature Cpp.isSorted : {T : Type} → [StrongOrd T] → List T → Bool

/-! ## Proven properties of cppMin -/

ProvenTheorem cppMin_cases :
    ∀ (a b : T), cppMin a b = a ∨ cppMin a b = b
ProvenTheorem cppMin_le_left :
    ∀ (a b : T), cmpLe (cppMin a b) a
ProvenTheorem cppMin_le_right :
    ∀ (a b : T), cmpLe (cppMin a b) b
ProvenTheorem cppMin_self :
    ∀ (a : T), cppMin a a = a
ProvenTheorem cppMin_comm :
    ∀ [StrongOrdEq T] (a b : T), cppMin a b = cppMin b a

/-! ## Proven properties of cppMax -/

ProvenTheorem cppMax_cases :
    ∀ (a b : T), cppMax a b = a ∨ cppMax a b = b
ProvenTheorem cppMax_ge_left :
    ∀ (a b : T), cmpLe a (cppMax a b)
ProvenTheorem cppMax_ge_right :
    ∀ (a b : T), cmpLe b (cppMax a b)
ProvenTheorem cppMax_self :
    ∀ (a : T), cppMax a a = a
ProvenTheorem cppMax_comm :
    ∀ [StrongOrdEq T] (a b : T), cppMax a b = cppMax b a

/-! ## Proven properties of cppClamp -/

ProvenTheorem cppClamp_trichotomy :
    ∀ (v lo hi : T), cppClamp v lo hi = lo ∨ cppClamp v lo hi = hi ∨ cppClamp v lo hi = v
ProvenTheorem cppClamp_in_range :
    ∀ (v lo hi : T), cmpLe lo hi →
      cmpLe lo (cppClamp v lo hi) ∧ cmpLe (cppClamp v lo hi) hi
ProvenTheorem cppClamp_lo :
    ∀ (lo hi : T), cmpLe lo hi → cppClamp lo lo hi = lo
ProvenTheorem cppClamp_hi :
    ∀ (lo hi : T), cmpLe lo hi → cppClamp hi lo hi = hi

/-! ## Proven properties of isSorted -/

ProvenTheorem isSorted_nil : isSorted ([] : List T) = true
ProvenTheorem isSorted_singleton : ∀ (a : T), isSorted [a] = true
ProvenTheorem isSorted_cons :
    ∀ (a b : T) (l : List T), isSorted (a :: b :: l) = true →
      StrongOrd.strongCmp a b ≠ Ordering.gt
ProvenTheorem isSorted_tail :
    ∀ (a b : T) (l : List T), isSorted (a :: b :: l) = true → isSorted (b :: l) = true

/-! ## Proven properties of minElement -/

ProvenTheorem minElement_mem :
    ∀ [Inhabited T] (l : List T), l ≠ [] → minElement l ∈ l
ProvenTheorem minElement_le :
    ∀ [Inhabited T] (l : List T), l ≠ [] →
      ∀ (x : T), x ∈ l → cmpLe (minElement l) x

/-! ## Tested conjectures -/

TestedConjecture cppMin_comm_nat :
    ∀ (a b : Nat), cppMin a b = cppMin b a
TestedConjecture cppMax_comm_nat :
    ∀ (a b : Nat), cppMax a b = cppMax b a
TestedConjecture cppClamp_in_range_nat :
    ∀ (v lo hi : Nat), cmpLe lo hi →
      cmpLe lo (cppClamp v lo hi) ∧ cmpLe (cppClamp v lo hi) hi

end Cpp
