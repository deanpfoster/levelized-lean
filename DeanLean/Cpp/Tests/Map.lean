import DeanLean.Basic
import DeanLean.Cpp.Code.Map

/-! # Tests for C++ sorted associative containers (N4950 §24.4) -/

namespace Cpp.Map.Tests

/-! ## Map basic operations -/

#eval do
  -- Empty map has no entries
  let m : Map Nat Nat := Map.empty
  assert! m.size == 0
  assert! m.find 1 == none
  assert! m.contains 1 == false

#eval do
  -- Insert and find
  let m := (Map.empty : Map Nat Nat).insert 3 30
  assert! m.find 3 == some 30
  assert! m.find 1 == none
  assert! m.contains 3 == true
  assert! m.contains 1 == false
  assert! m.size == 1

#eval do
  -- Multiple inserts
  let m := ((Map.empty : Map Nat Nat).insert 3 30).insert 1 10
  assert! m.find 1 == some 10
  assert! m.find 3 == some 30
  assert! m.size == 2

#eval do
  -- Insert then insert (overwrite)
  let m := ((Map.empty : Map Nat Nat).insert 3 30).insert 3 99
  assert! m.find 3 == some 99
  assert! m.size == 1

#eval do
  -- Insert multiple keys in various orders
  let m := ((((Map.empty : Map Nat Nat).insert 5 50).insert 2 20).insert 8 80).insert 1 10
  assert! m.find 1 == some 10
  assert! m.find 2 == some 20
  assert! m.find 5 == some 50
  assert! m.find 8 == some 80
  assert! m.find 3 == none
  assert! m.size == 4

#eval do
  -- Keys and values
  let m := (((Map.empty : Map Nat Nat).insert 3 30).insert 1 10).insert 2 20
  assert! m.keys == [1, 2, 3]
  assert! m.values == [10, 20, 30]

/-! ## Erase tests -/

#eval do
  -- Erase from single-element map
  let m := (Map.empty : Map Nat Nat).insert 3 30
  let m2 := m.erase 3
  assert! m2.find 3 == none
  assert! m2.size == 0

#eval do
  -- Erase non-existent key
  let m := (Map.empty : Map Nat Nat).insert 3 30
  let m2 := m.erase 5
  assert! m2.find 3 == some 30
  assert! m2.size == 1

#eval do
  -- Erase middle element
  let m := (((Map.empty : Map Nat Nat).insert 1 10).insert 3 30).insert 5 50
  let m2 := m.erase 3
  assert! m2.find 1 == some 10
  assert! m2.find 3 == none
  assert! m2.find 5 == some 50
  assert! m2.size == 2

#eval do
  -- Erase first element
  let m := (((Map.empty : Map Nat Nat).insert 1 10).insert 3 30).insert 5 50
  let m2 := m.erase 1
  assert! m2.find 1 == none
  assert! m2.find 3 == some 30
  assert! m2.find 5 == some 50
  assert! m2.size == 2

#eval do
  -- Erase last element
  let m := (((Map.empty : Map Nat Nat).insert 1 10).insert 3 30).insert 5 50
  let m2 := m.erase 5
  assert! m2.find 1 == some 10
  assert! m2.find 3 == some 30
  assert! m2.find 5 == none
  assert! m2.size == 2

end Cpp.Map.Tests

/-! ## CppSet tests -/

namespace Cpp.CppSet.Tests

#eval do
  -- Empty set
  let s : CppSet Nat := CppSet.empty
  assert! s.size == 0
  assert! s.contains 1 == false

#eval do
  -- Insert and contains
  let s := (CppSet.empty : CppSet Nat).insert 3
  assert! s.contains 3 == true
  assert! s.contains 1 == false
  assert! s.size == 1

#eval do
  -- Multiple inserts
  let s := ((CppSet.empty : CppSet Nat).insert 3).insert 1
  assert! s.contains 1 == true
  assert! s.contains 3 == true
  assert! s.size == 2

#eval do
  -- Duplicate insert (no-op)
  let s := ((CppSet.empty : CppSet Nat).insert 3).insert 3
  assert! s.contains 3 == true
  assert! s.size == 1

#eval do
  -- Insert multiple in various orders
  let s := ((((CppSet.empty : CppSet Nat).insert 5).insert 2).insert 8).insert 1
  assert! s.contains 1 == true
  assert! s.contains 2 == true
  assert! s.contains 5 == true
  assert! s.contains 8 == true
  assert! s.contains 3 == false
  assert! s.size == 4

#eval do
  -- Erase
  let s := (((CppSet.empty : CppSet Nat).insert 1).insert 3).insert 5
  let s2 := s.erase 3
  assert! s2.contains 1 == true
  assert! s2.contains 3 == false
  assert! s2.contains 5 == true
  assert! s2.size == 2

#eval do
  -- Erase non-existent
  let s := (CppSet.empty : CppSet Nat).insert 3
  let s2 := s.erase 5
  assert! s2.contains 3 == true
  assert! s2.size == 1

end Cpp.CppSet.Tests

/-! ## Named test defs for TestedConjectures -/

namespace Cpp

Test find_insert_same_nat :=
  show ((Map.empty : Map Nat Nat).insert 3 30).find 3 = some 30 from rfl

Test find_insert_other_nat :=
  show ((Map.empty : Map Nat Nat).insert 3 30).find 5 = none from rfl

Test find_empty_nat :=
  show (Map.empty : Map Nat Nat).find 1 = none from rfl

Test size_empty_nat :=
  show (Map.empty : Map Nat Nat).size = 0 from rfl

Test erase_find_nat :=
  show (((Map.empty : Map Nat Nat).insert 3 30).erase 3).find 3 = none from rfl

Test keys_sorted_nat :=
  show ((((Map.empty : Map Nat Nat).insert 5 50).insert 3 30).insert 1 10).keys = [1, 3, 5] from rfl

Test contains_insert_nat :=
  show ((CppSet.empty : CppSet Nat).insert 3).contains 3 = true from rfl

Test contains_erase_nat :=
  show (((CppSet.empty : CppSet Nat).insert 3).erase 3).contains 3 = false from rfl

Test contains_insert_other_nat :=
  show ((CppSet.empty : CppSet Nat).insert 3).contains 5 = false from rfl

Test insert_overwrite :=
  show (((Map.empty : Map Nat Nat).insert 3 30).insert 3 99).find 3 = some 99 from rfl

Test set_duplicate_insert :=
  show (((CppSet.empty : CppSet Nat).insert 3).insert 3).size = 1 from rfl

end Cpp
