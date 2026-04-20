import DeanLean.Cpp.Code.Sort

namespace Cpp.Sort

/-! # Proofs for sorting formalization

  Proves that `insertionSort` produces sorted output that is a permutation
  of the input. Also proves the reflection lemma connecting `isSorted` (Bool)
  with `IsSorted` (Prop).
-/

/-! ## Helper lemmas for insert -/

/-- Inserting into a sorted list produces a sorted list. -/
theorem insert_sorted (n : Nat) (l : List Nat) (hs : IsSorted l) :
    IsSorted (insert n l) := by
  induction hs with
  | nil =>
    -- l = [], insert n [] = [n]
    exact IsSorted.single n
  | single m =>
    -- l = [m]
    unfold insert
    split
    case isTrue h =>
      exact IsSorted.cons n m [] h (IsSorted.single m)
    case isFalse h =>
      unfold insert
      exact IsSorted.cons m n [] (Nat.le_of_lt (Nat.lt_of_not_le h)) (IsSorted.single n)
  | @cons a b rest hab hrest ih =>
    -- l = a :: b :: rest, a ≤ b, IsSorted (b :: rest)
    -- ih : IsSorted (insert n (b :: rest))
    unfold insert
    split
    case isTrue hna =>
      -- n ≤ a
      exact IsSorted.cons n a (b :: rest) hna (IsSorted.cons a b rest hab hrest)
    case isFalse hna =>
      -- ¬(n ≤ a), so a < n
      have han : a ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hna)
      -- Goal: IsSorted (a :: insert n (b :: rest))
      -- ih : IsSorted (insert n (b :: rest))
      -- Case split on whether n ≤ b, using a decidable instance
      by_cases hnb : n ≤ b
      case pos =>
        -- n ≤ b, so insert n (b :: rest) = n :: b :: rest
        simp [insert, hnb]
        exact IsSorted.cons a n (b :: rest) han (IsSorted.cons n b rest hnb hrest)
      case neg =>
        -- ¬(n ≤ b), so insert n (b :: rest) = b :: insert n rest
        simp [insert, hnb] at ih ⊢
        exact IsSorted.cons a b (insert n rest) hab ih

/-- `insert n l` is a permutation of `n :: l`. -/
theorem insert_perm (n : Nat) (l : List Nat) :
    (insert n l).Perm (n :: l) := by
  induction l with
  | nil =>
    unfold insert
    exact List.Perm.refl _
  | cons x xs ih =>
    unfold insert
    split
    case isTrue h =>
      exact List.Perm.refl _
    case isFalse h =>
      -- (x :: insert n xs).Perm (n :: x :: xs)
      -- ih : (insert n xs).Perm (n :: xs)
      exact (List.Perm.cons x ih).trans (List.Perm.swap n x xs)

/-- Length of `insert n l` is `l.length + 1`. -/
theorem insert_length (n : Nat) (l : List Nat) :
    (insert n l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold insert
    split
    case isTrue h => simp [List.length]
    case isFalse h => simp [List.length, ih]

/-! ## Main theorems -/

/-- Insertion sort produces a sorted list. -/
theorem insertionSort_sorted_proof (l : List Nat) :
    IsSorted (insertionSort l) := by
  induction l with
  | nil => exact IsSorted.nil
  | cons x xs ih =>
    exact insert_sorted x (insertionSort xs) ih

/-- Insertion sort produces a permutation of the input. -/
theorem insertionSort_perm_proof (l : List Nat) :
    IsPermutation l (insertionSort l) := by
  unfold IsPermutation
  induction l with
  | nil => exact List.Perm.nil
  | cons x xs ih =>
    -- Need: (x :: xs).Perm (insert x (insertionSort xs))
    exact (List.Perm.cons x ih).trans (insert_perm x (insertionSort xs)).symm

/-- Insertion sort preserves length. -/
theorem insertionSort_length_proof (l : List Nat) :
    (insertionSort l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [insertionSort, insert_length, ih]

/-! ## isSorted ↔ IsSorted reflection -/

/-- If `isSorted l = true` then `IsSorted l`. -/
theorem isSorted_true_imp_IsSorted (l : List Nat) (h : isSorted l = true) :
    IsSorted l := by
  induction l with
  | nil => exact IsSorted.nil
  | cons x xs ih =>
    cases xs with
    | nil => exact IsSorted.single x
    | cons y ys =>
      unfold isSorted at h
      split at h
      case isTrue hxy =>
        exact IsSorted.cons x y ys hxy (ih h)
      case isFalse hxy =>
        exact absurd h (by decide)

/-- If `IsSorted l` then `isSorted l = true`. -/
theorem IsSorted_imp_isSorted_true (l : List Nat) (h : IsSorted l) :
    isSorted l = true := by
  induction h with
  | nil => rfl
  | single n => rfl
  | cons a b l hab hsorted ih =>
    unfold isSorted
    split
    case isTrue h => exact ih
    case isFalse h => exact absurd hab h

/-- Reflection: `isSorted l = true ↔ IsSorted l`. -/
theorem isSorted_iff_IsSorted_proof (l : List Nat) :
    isSorted l = true ↔ IsSorted l :=
  ⟨isSorted_true_imp_IsSorted l, IsSorted_imp_isSorted_true l⟩

end Cpp.Sort
