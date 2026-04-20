import DeanLean.Basic

namespace Cpp.Sort

/-! # Sorting algorithms formalized in Lean 4

  Defines insertion sort on `List Nat` with the predicates needed
  to state correctness:
  - `IsSorted` — the inductive "each element ≤ the next" property
  - `IsPermutation` — wrapper around `List.Perm`
  - `insertionSort` — classic insertion sort
  - `isSorted` — decidable Boolean check
-/

/-! ## IsSorted predicate (inductive, on List Nat) -/

/-- A list of natural numbers is sorted in non-decreasing order. -/
inductive IsSorted : List Nat → Prop where
  | nil  : IsSorted []
  | single (n : Nat) : IsSorted [n]
  | cons (a b : Nat) (l : List Nat) :
      a ≤ b → IsSorted (b :: l) → IsSorted (a :: b :: l)

/-! ## IsPermutation -/

/-- Two lists are permutations of each other (same elements, same multiplicities).
    We use Lean's standard library `List.Perm`. -/
def IsPermutation (l₁ l₂ : List Nat) : Prop := l₁.Perm l₂

/-! ## isSorted (decidable Boolean check) -/

/-- Decidable check: is a `List Nat` sorted in non-decreasing order? -/
def isSorted : List Nat → Bool
  | []  => true
  | [_] => true
  | a :: b :: rest =>
    if a ≤ b then isSorted (b :: rest) else false

/-! ## Insertion sort -/

/-- Insert a natural number into a sorted list, maintaining sorted order. -/
def insert (n : Nat) : List Nat → List Nat
  | [] => [n]
  | x :: xs =>
    if n ≤ x then n :: x :: xs
    else x :: insert n xs

/-- Insertion sort on `List Nat`. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

end Cpp.Sort
