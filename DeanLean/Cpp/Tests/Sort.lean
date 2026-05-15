import DeanLean.Basic
import DeanLean.Cpp.Code.Sort
import DeanLean.Cpp.Proofs.Sort

namespace Cpp.Sort.Tests

/-! # Tests for sorting formalization

  Executable tests using `#eval` and `assert!`, plus named `_test` definitions
  for use with `TestedConjecture` in the header file.
-/

/-! ## insertionSort tests -/

#eval do
  assert! insertionSort [] == []
  assert! insertionSort [1] == [1]
  assert! insertionSort [2, 1] == [1, 2]
  assert! insertionSort [3, 1, 2] == [1, 2, 3]
  assert! insertionSort [5, 3, 8, 1, 2] == [1, 2, 3, 5, 8]
  assert! insertionSort [1, 1, 1] == [1, 1, 1]
  assert! insertionSort [3, 1, 4, 1, 5, 9, 2, 6] == [1, 1, 2, 3, 4, 5, 6, 9]

/-! ## isSorted tests -/

#eval do
  assert! isSorted [] == true
  assert! isSorted [42] == true
  assert! isSorted [1, 2, 3, 4, 5] == true
  assert! isSorted [1, 1, 2, 2, 3] == true
  assert! isSorted [3, 1, 2] == false
  assert! isSorted [5, 4, 3, 2, 1] == false

/-! ## isSorted after insertionSort -/

#eval do
  assert! isSorted (insertionSort [5, 3, 8, 1, 2]) == true
  assert! isSorted (insertionSort [3, 1, 4, 1, 5, 9, 2, 6]) == true
  assert! isSorted (insertionSort []) == true
  assert! isSorted (insertionSort [42]) == true

/-! ## Length preservation tests -/

#eval do
  assert! (insertionSort [5, 3, 8, 1, 2]).length == 5
  assert! (insertionSort []).length == 0
  assert! (insertionSort [1]).length == 1
  assert! (insertionSort [3, 1, 4, 1, 5, 9, 2, 6]).length == 8

end Cpp.Sort.Tests

/-! ## Named test definitions for TestedConjecture -/

namespace Cpp.Sort

Test insertionSort_sorted :=
  show isSorted (insertionSort [5, 3, 8, 1, 2]) = true from rfl

Test insertionSort_length :=
  show (insertionSort [5, 3, 8, 1, 2]).length = 5 from rfl

Test insertionSort_perm :=
  show insertionSort [3, 1, 2] = [1, 2, 3] from rfl

Test isSorted_iff_IsSorted :=
  show isSorted [1, 2, 3] = true from rfl

end Cpp.Sort
