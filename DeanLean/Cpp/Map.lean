import DeanLean.Cpp.Defs.Map
import DeanLean.Cpp.Proofs.Map
import DeanLean.Cpp.Tests.Map

/-! # C++ sorted associative containers (N4950 §24.4)

  Formalizes simplified `std::map<K,V>` and `std::set<K>`:
  - `Map K V` — sorted list of key-value pairs with unique keys (§24.4.4)
  - `CppSet K` — sorted list of unique elements (§24.4.3)

  Both use `StrongOrd` for key comparison and maintain a sorted invariant.
  Operations: empty, insert, find, erase, contains, size, keys, values.

  The C++ spec defines these by their INVARIANTS (sorted, unique keys),
  not their implementation. We model them using sorted `List` for provability.
-/

namespace Cpp

variable {K : Type} {V : Type} [StrongOrd K]

/-! ## Vocabulary — definitions that appear in theorem types

  SortedKeys [StrongOrd K] : List K → Prop
    Each adjacent pair has strongCmp k₁ k₂ = .lt (strictly ascending)

  Map K V [StrongOrd K] : structure with entries : List (K × V)
    and proof that entries satisfies SortedPairs

  CppSet K [StrongOrd K] : structure with elems : List K
    and proof that elems satisfies SortedKeys
-/

/-! ## Map type signatures -/

Signature Cpp.Map.empty : Map K V
Signature Cpp.Map.insert : Map K V → K → V → Map K V
Signature Cpp.Map.find : Map K V → K → Option V
Signature Cpp.Map.erase : Map K V → K → Map K V
Signature Cpp.Map.contains : Map K V → K → Bool
Signature Cpp.Map.size : Map K V → Nat
Signature Cpp.Map.keys : Map K V → List K
Signature Cpp.Map.values : Map K V → List V

/-! ## Map: proven theorems -/

ProvenTheorem find_insert_same : ∀ (m : Map K V) (k : K) (v : V),
    (m.insert k v).find k = some v

ProvenTheorem find_insert_other : ∀ (m : Map K V) (k₁ k₂ : K) (v : V),
    StrongOrd.strongCmp k₁ k₂ ≠ .eq →
    (m.insert k₁ v).find k₂ = m.find k₂

ProvenTheorem find_empty : ∀ (k : K),
    (Map.empty : Map K V).find k = none

ProvenTheorem contains_iff_find : ∀ (m : Map K V) (k : K),
    m.contains k = true ↔ ∃ v, m.find k = some v

ProvenTheorem size_empty : (Map.empty : Map K V).size = 0

ProvenTheorem erase_find : ∀ (m : Map K V) (k : K),
    (m.erase k).find k = none

ProvenTheorem keys_sorted : ∀ (m : Map K V), SortedKeys m.keys

/-! ## CppSet type signatures -/

Signature Cpp.CppSet.empty : CppSet K
Signature Cpp.CppSet.insert : CppSet K → K → CppSet K
Signature Cpp.CppSet.contains : CppSet K → K → Bool
Signature Cpp.CppSet.erase : CppSet K → K → CppSet K
Signature Cpp.CppSet.size : CppSet K → Nat

/-! ## CppSet: proven theorems -/

ProvenTheorem contains_insert : ∀ (s : CppSet K) (k : K),
    (s.insert k).contains k = true

ProvenTheorem contains_erase : ∀ (s : CppSet K) (k : K),
    (s.erase k).contains k = false

ProvenTheorem contains_insert_other : ∀ (s : CppSet K) (k₁ k₂ : K),
    StrongOrd.strongCmp k₁ k₂ ≠ .eq →
    (s.insert k₁).contains k₂ = s.contains k₂

/-! ## Tested conjectures -/

TestedConjecture find_insert_same_nat :
    ((Map.empty : Map Nat Nat).insert 3 30).find 3 = some 30

TestedConjecture find_insert_other_nat :
    ((Map.empty : Map Nat Nat).insert 3 30).find 5 = none

TestedConjecture find_empty_nat :
    (Map.empty : Map Nat Nat).find 1 = none

TestedConjecture size_empty_nat :
    (Map.empty : Map Nat Nat).size = 0

TestedConjecture erase_find_nat :
    (((Map.empty : Map Nat Nat).insert 3 30).erase 3).find 3 = none

TestedConjecture keys_sorted_nat :
    ((((Map.empty : Map Nat Nat).insert 5 50).insert 3 30).insert 1 10).keys = [1, 3, 5]

TestedConjecture contains_insert_nat :
    ((CppSet.empty : CppSet Nat).insert 3).contains 3 = true

TestedConjecture contains_erase_nat :
    (((CppSet.empty : CppSet Nat).insert 3).erase 3).contains 3 = false

TestedConjecture contains_insert_other_nat :
    ((CppSet.empty : CppSet Nat).insert 3).contains 5 = false

TestedConjecture insert_overwrite :
    (((Map.empty : Map Nat Nat).insert 3 30).insert 3 99).find 3 = some 99

TestedConjecture set_duplicate_insert :
    (((CppSet.empty : CppSet Nat).insert 3).insert 3).size = 1

end Cpp
