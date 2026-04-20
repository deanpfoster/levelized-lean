import DeanLean.Cpp.Code.Vector

namespace Cpp.Vector.Tests

open Cpp.Vector in
#eval do
  -- empty vector
  let v : Vector Nat := Vector.empty
  assert! v.size == 0
  assert! v.isEmpty == true

  -- push_back
  let v := v.push_back 10
  assert! v.size == 1
  assert! v.isEmpty == false

  let v := v.push_back 20
  let v := v.push_back 30
  assert! v.size == 3

  -- indexed access
  assert! v.data[0]! == 10
  assert! v.data[1]! == 20
  assert! v.data[2]! == 30

  -- front and back
  assert! v.data[0]! == 10
  assert! v.data[v.data.size - 1]! == 30

  -- pop_back
  let v2 := v.pop_back
  assert! v2.size == 2
  assert! v2.data[0]! == 10
  assert! v2.data[1]! == 20

  -- clear
  let v3 := v.clear
  assert! v3.size == 0
  assert! v3.isEmpty == true

  -- push_back then pop_back roundtrip
  let v4 := v.pop_back
  assert! v4.size == 2
  let v5 := v4.push_back v.data[v.data.size - 1]!
  assert! v5.size == v.size
  assert! v5 == v

open Cpp.Vector in
#eval do
  -- insert: start with [1, 3, 4], insert 2 at position 1 → [1, 2, 3, 4]
  let v : Vector Nat := Vector.empty.push_back 1 |>.push_back 3 |>.push_back 4
  -- manually construct inserted vector
  let left := v.data.extract 0 1
  let right := v.data.extract 1 v.data.size
  let v2 : Vector Nat := ⟨(left.push 2) ++ right⟩
  assert! v2.size == 4
  assert! v2.data[0]! == 1
  assert! v2.data[1]! == 2
  assert! v2.data[2]! == 3
  assert! v2.data[3]! == 4

  -- erase: from [1, 2, 3, 4], erase index 1 → [1, 3, 4]
  let v3 : Vector Nat := ⟨v2.data.eraseIdx 1⟩
  assert! v3.size == 3
  assert! v3.data[0]! == 1
  assert! v3.data[1]! == 3
  assert! v3.data[2]! == 4

open Cpp.Vector in
#eval do
  -- ofList / toList roundtrip
  let l := [5, 10, 15, 20]
  let v := Vector.ofList l
  assert! v.size == 4
  assert! v.toList == l

  -- ofArray / toArray roundtrip
  let a : Array Nat := #[100, 200, 300]
  let v := Vector.ofArray a
  assert! v.toArray == a
  assert! v.size == 3

end Cpp.Vector.Tests
