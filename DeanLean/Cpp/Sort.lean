import DeanLean.Cpp.Defs.Sort
import DeanLean.Cpp.Proofs.SortExports

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

/-! ## Vocabulary (imported from Defs/Sort.lean — all names used in theorems below)

  IsSorted : List Nat → Prop       — inductive: nil, single, cons (a ≤ b → ...)
  IsPermutation l₁ l₂ := l₁.Perm l₂
  isSorted : List Nat → Bool       — decidable check
  insertionSort : List Nat → List Nat
-/

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
