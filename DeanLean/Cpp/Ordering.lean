import DeanLean.Cpp.Defs.Ordering
import DeanLean.Cpp.Proofs.Ordering
import DeanLean.Cpp.Tests.Ordering

/-! # C++ comparison/ordering types (N4950 §17.11)

  Formalizes the three comparison category types from `<compare>`:
  - `Ordering` (strong_ordering, §17.11.2.4): lt, eq, gt
  - `WeakOrdering` (weak_ordering, §17.11.2.3): lt, equivalent, gt
  - `PartialOrdering` (partial_ordering, §17.11.2.2): lt, equivalent, gt, unordered

  Also provides the `StrongOrd` typeclass with comparison laws
  (reflexivity, flip, lt-transitivity, eq-transitivity),
  instances for Nat and Int, and a lexicographic lifting for Pair.

  This is the FOUNDATION of the ordering dependency chain.
  FunctionObjects and Algorithm modules import and use these theorems.
-/

namespace Cpp

variable {T : Type} [StrongOrd T]

/-! ## Vocabulary — definitions that appear in theorem types

  inductive Ordering := lt | eq | gt       (C++ strong_ordering)
  inductive WeakOrdering := lt | equivalent | gt
  inductive PartialOrdering := lt | equivalent | gt | unordered

  class StrongOrd (T : Type) where
    strongCmp : T → T → Ordering
    cmp_refl : ∀ a, strongCmp a a = .eq
    cmp_flip : ∀ a b, (strongCmp a b).flip = strongCmp b a
    cmp_lt_trans : ∀ a b c, strongCmp a b = .lt → strongCmp b c = .lt → strongCmp a c = .lt
    cmp_eq_trans : ∀ a b c, strongCmp a b = .eq → strongCmp b c = .eq → strongCmp a c = .eq
  Instances: Nat, Int, Pair T1 T2 (lexicographic)
-/

/-! ## Type signatures -/

Signature Cpp.Ordering.flip : Ordering → Ordering
Signature Cpp.Ordering.toWeak : Ordering → WeakOrdering
Signature Cpp.Ordering.toPartial : Ordering → PartialOrdering
Signature Cpp.Ordering.is_eq : Ordering → Bool
Signature Cpp.Ordering.is_neq : Ordering → Bool
Signature Cpp.Ordering.is_lt : Ordering → Bool
Signature Cpp.Ordering.is_lteq : Ordering → Bool
Signature Cpp.Ordering.is_gt : Ordering → Bool
Signature Cpp.Ordering.is_gteq : Ordering → Bool
Signature Cpp.WeakOrdering.toPartial : WeakOrdering → PartialOrdering
Signature Cpp.PartialOrdering.is_eq : PartialOrdering → Bool
Signature Cpp.PartialOrdering.is_lt : PartialOrdering → Bool
Signature Cpp.PartialOrdering.is_gt : PartialOrdering → Bool
Signature Cpp.natCmp : Nat → Nat → Ordering
Signature Cpp.intCmp : Int → Int → Ordering

/-! ## Proven theorems: Ordering type properties -/

ProvenTheorem flip_flip : ∀ (o : Ordering), o.flip.flip = o
ProvenTheorem flip_lt : Ordering.lt.flip = Ordering.gt
ProvenTheorem flip_eq : Ordering.eq.flip = Ordering.eq
ProvenTheorem flip_gt : Ordering.gt.flip = Ordering.lt

ProvenTheorem toWeak_lt : Ordering.lt.toWeak = WeakOrdering.lt
ProvenTheorem toWeak_eq : Ordering.eq.toWeak = WeakOrdering.equivalent
ProvenTheorem toWeak_gt : Ordering.gt.toWeak = WeakOrdering.gt

ProvenTheorem toPartial_lt : Ordering.lt.toPartial = PartialOrdering.lt
ProvenTheorem toPartial_eq : Ordering.eq.toPartial = PartialOrdering.equivalent
ProvenTheorem toPartial_gt : Ordering.gt.toPartial = PartialOrdering.gt

/-! ## Proven theorems: StrongOrd laws -/

ProvenTheorem strongCmp_refl : ∀ (a : T), StrongOrd.strongCmp a a = .eq
ProvenTheorem strongCmp_flip : ∀ (a b : T),
    (StrongOrd.strongCmp a b).flip = StrongOrd.strongCmp b a
ProvenTheorem strongCmp_lt_trans : ∀ (a b c : T),
    StrongOrd.strongCmp a b = .lt → StrongOrd.strongCmp b c = .lt →
    StrongOrd.strongCmp a c = .lt
ProvenTheorem strongCmp_gt_trans : ∀ (a b c : T),
    StrongOrd.strongCmp a b = .gt → StrongOrd.strongCmp b c = .gt →
    StrongOrd.strongCmp a c = .gt
ProvenTheorem strongCmp_eq_trans : ∀ (a b c : T),
    StrongOrd.strongCmp a b = .eq → StrongOrd.strongCmp b c = .eq →
    StrongOrd.strongCmp a c = .eq
ProvenTheorem strongCmp_eq_symm : ∀ (a b : T),
    StrongOrd.strongCmp a b = .eq → StrongOrd.strongCmp b a = .eq
ProvenTheorem strongCmp_lt_eq_trans : ∀ (a b c : T),
    StrongOrd.strongCmp a b = .lt → StrongOrd.strongCmp b c = .eq →
    StrongOrd.strongCmp a c = .lt
ProvenTheorem strongCmp_eq_lt_trans : ∀ (a b c : T),
    StrongOrd.strongCmp a b = .eq → StrongOrd.strongCmp b c = .lt →
    StrongOrd.strongCmp a c = .lt
ProvenTheorem strongCmp_trichotomy : ∀ (a b : T),
    StrongOrd.strongCmp a b = .lt ∨
    StrongOrd.strongCmp a b = .eq ∨
    StrongOrd.strongCmp a b = .gt
ProvenTheorem strongCmp_lt_iff_gt : ∀ (a b : T),
    StrongOrd.strongCmp a b = .lt ↔ StrongOrd.strongCmp b a = .gt

/-! ## Proven theorems: Nat instance -/

ProvenTheorem nat_cmp_zero_zero : natCmp 0 0 = .eq
ProvenTheorem nat_cmp_lt : ∀ (a b : Nat), a < b → natCmp a b = .lt
ProvenTheorem nat_cmp_eq : ∀ (a b : Nat), a = b → natCmp a b = .eq
ProvenTheorem nat_cmp_gt : ∀ (a b : Nat), b < a → natCmp a b = .gt

/-! ## Proven theorems: Int instance -/

ProvenTheorem int_cmp_zero_zero : intCmp 0 0 = .eq
ProvenTheorem int_cmp_lt : ∀ (a b : Int), a < b → intCmp a b = .lt
ProvenTheorem int_cmp_eq : ∀ (a b : Int), a = b → intCmp a b = .eq
ProvenTheorem int_cmp_gt : ∀ (a b : Int), b < a → intCmp a b = .gt

/-! ## Proven theorems: Pair lexicographic ordering -/

variable {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2]

ProvenTheorem pair_cmp_first_lt : ∀ (p q : Pair T1 T2),
    StrongOrd.strongCmp p.first q.first = .lt →
    StrongOrd.strongCmp p q = .lt
ProvenTheorem pair_cmp_first_gt : ∀ (p q : Pair T1 T2),
    StrongOrd.strongCmp p.first q.first = .gt →
    StrongOrd.strongCmp p q = .gt
ProvenTheorem pair_cmp_first_eq : ∀ (p q : Pair T1 T2),
    StrongOrd.strongCmp p.first q.first = .eq →
    StrongOrd.strongCmp p q = StrongOrd.strongCmp p.second q.second
ProvenTheorem pair_cmp_eq_iff : ∀ (p q : Pair T1 T2),
    StrongOrd.strongCmp p q = .eq ↔
    (StrongOrd.strongCmp p.first q.first = .eq ∧
     StrongOrd.strongCmp p.second q.second = .eq)

/-! ## Tested conjectures -/

TestedConjecture strongCmp_refl_nat :
    StrongOrd.strongCmp 42 42 = Ordering.eq
TestedConjecture strongCmp_flip_nat :
    (StrongOrd.strongCmp 3 7).flip = StrongOrd.strongCmp 7 3
TestedConjecture strongCmp_lt_trans_nat :
    StrongOrd.strongCmp 1 3 = Ordering.lt
TestedConjecture strongCmp_refl_int :
    StrongOrd.strongCmp (-5 : Int) (-5) = Ordering.eq
TestedConjecture strongCmp_flip_int :
    (StrongOrd.strongCmp (1 : Int) (2 : Int)).flip = StrongOrd.strongCmp 2 1
TestedConjecture strongCmp_refl_pair :
    StrongOrd.strongCmp (Pair.make 1 2) (Pair.make 1 2) = Ordering.eq
TestedConjecture strongCmp_flip_pair :
    (StrongOrd.strongCmp (Pair.make 1 2) (Pair.make 1 3)).flip =
     StrongOrd.strongCmp (Pair.make 1 3) (Pair.make 1 2)
TestedConjecture strongCmp_lt_trans_pair :
    StrongOrd.strongCmp (Pair.make 1 2) (Pair.make 2 1) = Ordering.lt
TestedConjecture flip_involution :
    Ordering.lt.flip.flip = Ordering.lt
TestedConjecture toWeak_preserves :
    Ordering.lt.toWeak = WeakOrdering.lt
TestedConjecture toPartial_preserves :
    Ordering.lt.toPartial = PartialOrdering.lt

end Cpp
