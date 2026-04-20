import DeanLean.Cpp.Code.Variant
import DeanLean.Cpp.Proofs.Variant
import DeanLean.Cpp.Tests.Variant

/-! # C++ std::variant (§22.6)

  Type-safe tagged union that holds a value of one of its alternative types.
  Variant2 models variant<T1,T2>, Variant3 models variant<T1,T2,T3>.
  Corresponds to N4950 §22.6.1–22.6.7.
-/

namespace Cpp.Variant2

variable {T1 T2 R : Type}

Signature Cpp.Variant2.index : Variant2 T1 T2 → Fin 2
Signature Cpp.Variant2.holds_alternative : Variant2 T1 T2 → Fin 2 → Bool
Signature Cpp.Variant2.valueless_by_exception : Variant2 T1 T2 → Bool
Signature Cpp.Variant2.visit : (T1 → R) → (T2 → R) → Variant2 T1 T2 → R
Signature Cpp.Variant2.variant_size : Variant2 T1 T2 → Nat

-- index correctness
ProvenTheorem index_first : ∀ (v : T1),
    (Variant2.first v : Variant2 T1 T2).index = ⟨0, by omega⟩
ProvenTheorem index_second : ∀ (v : T2),
    (Variant2.second v : Variant2 T1 T2).index = ⟨1, by omega⟩

-- holds_alternative correctness
ProvenTheorem holds_alternative_first_0 : ∀ (v : T1),
    (Variant2.first v : Variant2 T1 T2).holds_alternative ⟨0, by omega⟩ = true
ProvenTheorem holds_alternative_first_1 : ∀ (v : T1),
    (Variant2.first v : Variant2 T1 T2).holds_alternative ⟨1, by omega⟩ = false
ProvenTheorem holds_alternative_second_1 : ∀ (v : T2),
    (Variant2.second v : Variant2 T1 T2).holds_alternative ⟨1, by omega⟩ = true
ProvenTheorem holds_alternative_second_0 : ∀ (v : T2),
    (Variant2.second v : Variant2 T1 T2).holds_alternative ⟨0, by omega⟩ = false

-- get roundtrips
ProvenTheorem get_first_roundtrip : ∀ (v : T1),
    let w : Variant2 T1 T2 := Variant2.first v
    w.get_first (index_first_proof v) = v
ProvenTheorem get_second_roundtrip : ∀ (v : T2),
    let w : Variant2 T1 T2 := Variant2.second v
    w.get_second (index_second_proof v) = v

-- visit roundtrips
ProvenTheorem visit_first : ∀ (v : T1) {R : Type} (f1 : T1 → R) (f2 : T2 → R),
    (Variant2.first v : Variant2 T1 T2).visit f1 f2 = f1 v
ProvenTheorem visit_second : ∀ (v : T2) {R : Type} (f1 : T1 → R) (f2 : T2 → R),
    (Variant2.second v : Variant2 T1 T2).visit f1 f2 = f2 v

-- visit composition
ProvenTheorem visit_compose : ∀ {R S : Type} (f1 : T1 → R) (f2 : T2 → R) (g : R → S)
    (w : Variant2 T1 T2),
    w.visit (g ∘ f1) (g ∘ f2) = g (w.visit f1 f2)

-- valueless_by_exception always false
ProvenTheorem valueless_by_exception_false : ∀ (w : Variant2 T1 T2),
    w.valueless_by_exception = false

-- variant_size
ProvenTheorem variant_size_eq : ∀ (w : Variant2 T1 T2), w.variant_size = 2

/-! ## Variant2 discriminator properties (tested) -/

TestedConjecture index_determines_alternative : ∀ (w : Variant2 T1 T2) (i : Fin 2),
    w.holds_alternative i = (w.index == i)

TestedConjecture exactly_one_alternative : ∀ (w : Variant2 T1 T2),
    w.holds_alternative ⟨0, by omega⟩ != w.holds_alternative ⟨1, by omega⟩

TestedConjecture different_constructors_different_index :
    ∀ (v1 : T1) (v2 : T2),
    (Variant2.first v1 : Variant2 T1 T2).index ≠ (Variant2.second v2 : Variant2 T1 T2).index

/-! ## visit is the universal eliminator (tested) -/

TestedConjecture visit_determines_equality :
    ∀ [DecidableEq R] (f1 : T1 → R) (f2 : T2 → R) (w1 w2 : Variant2 T1 T2),
    w1 = w2 → w1.visit f1 f2 = w2.visit f1 f2

end Cpp.Variant2

namespace Cpp.Variant3

variable {T1 T2 T3 R : Type}

Signature Cpp.Variant3.index : Variant3 T1 T2 T3 → Fin 3
Signature Cpp.Variant3.holds_alternative : Variant3 T1 T2 T3 → Fin 3 → Bool
Signature Cpp.Variant3.valueless_by_exception : Variant3 T1 T2 T3 → Bool
Signature Cpp.Variant3.visit : (T1 → R) → (T2 → R) → (T3 → R) → Variant3 T1 T2 T3 → R
Signature Cpp.Variant3.variant_size : Variant3 T1 T2 T3 → Nat

-- index correctness
ProvenTheorem index_first : ∀ (v : T1),
    (Variant3.first v : Variant3 T1 T2 T3).index = ⟨0, by omega⟩
ProvenTheorem index_second : ∀ (v : T2),
    (Variant3.second v : Variant3 T1 T2 T3).index = ⟨1, by omega⟩
ProvenTheorem index_third : ∀ (v : T3),
    (Variant3.third v : Variant3 T1 T2 T3).index = ⟨2, by omega⟩

-- holds_alternative correctness
ProvenTheorem holds_alternative_first_0 : ∀ (v : T1),
    (Variant3.first v : Variant3 T1 T2 T3).holds_alternative ⟨0, by omega⟩ = true
ProvenTheorem holds_alternative_second_1 : ∀ (v : T2),
    (Variant3.second v : Variant3 T1 T2 T3).holds_alternative ⟨1, by omega⟩ = true
ProvenTheorem holds_alternative_third_2 : ∀ (v : T3),
    (Variant3.third v : Variant3 T1 T2 T3).holds_alternative ⟨2, by omega⟩ = true

-- get roundtrips
ProvenTheorem get_first_roundtrip : ∀ (v : T1),
    let w : Variant3 T1 T2 T3 := Variant3.first v
    w.get_first (index_first_proof v) = v
ProvenTheorem get_second_roundtrip : ∀ (v : T2),
    let w : Variant3 T1 T2 T3 := Variant3.second v
    w.get_second (index_second_proof v) = v
ProvenTheorem get_third_roundtrip : ∀ (v : T3),
    let w : Variant3 T1 T2 T3 := Variant3.third v
    w.get_third (index_third_proof v) = v

-- visit roundtrips
ProvenTheorem visit_first : ∀ (v : T1) {R : Type} (f1 : T1 → R) (f2 : T2 → R) (f3 : T3 → R),
    (Variant3.first v : Variant3 T1 T2 T3).visit f1 f2 f3 = f1 v
ProvenTheorem visit_second : ∀ (v : T2) {R : Type} (f1 : T1 → R) (f2 : T2 → R) (f3 : T3 → R),
    (Variant3.second v : Variant3 T1 T2 T3).visit f1 f2 f3 = f2 v
ProvenTheorem visit_third : ∀ (v : T3) {R : Type} (f1 : T1 → R) (f2 : T2 → R) (f3 : T3 → R),
    (Variant3.third v : Variant3 T1 T2 T3).visit f1 f2 f3 = f3 v

-- visit composition
ProvenTheorem visit_compose : ∀ {R S : Type} (f1 : T1 → R) (f2 : T2 → R) (f3 : T3 → R)
    (g : R → S) (w : Variant3 T1 T2 T3),
    w.visit (g ∘ f1) (g ∘ f2) (g ∘ f3) = g (w.visit f1 f2 f3)

-- valueless_by_exception always false
ProvenTheorem valueless_by_exception_false : ∀ (w : Variant3 T1 T2 T3),
    w.valueless_by_exception = false

-- variant_size
ProvenTheorem variant_size_eq : ∀ (w : Variant3 T1 T2 T3), w.variant_size = 3

/-! ## Variant3 discriminator properties (tested) -/

TestedConjecture index_determines_alternative : ∀ (w : Variant3 T1 T2 T3) (i : Fin 3),
    w.holds_alternative i = (w.index == i)

TestedConjecture exactly_one_alternative : ∀ (w : Variant3 T1 T2 T3),
    (w.holds_alternative ⟨0, by omega⟩).toNat +
    (w.holds_alternative ⟨1, by omega⟩).toNat +
    (w.holds_alternative ⟨2, by omega⟩).toNat = 1

end Cpp.Variant3
