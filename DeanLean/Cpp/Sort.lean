import DeanLean.Cpp.Code.Sort
import DeanLean.Cpp.Proofs.Sort
import DeanLean.Cpp.Tests.Sort

/-! # Sorting algorithms formalized and verified

  Formalizes insertion sort on `List Nat` with full correctness proofs:
  - `IsSorted` — inductive predicate: each element ≤ the next
  - `IsPermutation` — same elements with same multiplicities (`List.Perm`)
  - `insertionSort` — classic insertion sort
  - `isSorted` — decidable Boolean sorted check

  Crown-jewel theorems:
  - `insertionSort_sorted` — output is sorted (proven by induction)
  - `insertionSort_perm` — output is a permutation of input (proven by induction)
  - `insertionSort_length` — output has same length (proven by induction)
  - `isSorted_iff_IsSorted` — Boolean check reflects inductive predicate
-/

namespace Cpp.Sort

/-! ## Signatures -/

Signature Cpp.Sort.isSorted : List Nat → Bool
Signature Cpp.Sort.insert : Nat → List Nat → List Nat
Signature Cpp.Sort.insertionSort : List Nat → List Nat

/-! ## Proven theorems: insertionSort correctness -/

ProvenTheorem insertionSort_sorted :
    ∀ (l : List Nat), IsSorted (insertionSort l)

ProvenTheorem insertionSort_perm :
    ∀ (l : List Nat), IsPermutation l (insertionSort l)

ProvenTheorem insertionSort_length :
    ∀ (l : List Nat), (insertionSort l).length = l.length

/-! ## Proven theorem: isSorted reflection -/

ProvenTheorem isSorted_iff_IsSorted :
    ∀ (l : List Nat), isSorted l = true ↔ IsSorted l

end Cpp.Sort
