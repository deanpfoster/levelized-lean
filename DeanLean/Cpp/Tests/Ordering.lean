import DeanLean.Basic
import DeanLean.Cpp.Code.Ordering

/-! # Tests for C++ comparison/ordering types (N4950 §17.11) -/

namespace Cpp.Ordering.Tests

/-! ## Ordering type basic tests -/

#eval do
  assert! Ordering.lt != Ordering.eq
  assert! Ordering.lt != Ordering.gt
  assert! Ordering.eq != Ordering.gt
  assert! Ordering.lt == Ordering.lt
  assert! Ordering.eq == Ordering.eq
  assert! Ordering.gt == Ordering.gt

/-! ## Flip tests -/

#eval do
  assert! Ordering.lt.flip == Ordering.gt
  assert! Ordering.eq.flip == Ordering.eq
  assert! Ordering.gt.flip == Ordering.lt
  assert! Ordering.lt.flip.flip == Ordering.lt
  assert! Ordering.eq.flip.flip == Ordering.eq
  assert! Ordering.gt.flip.flip == Ordering.gt

/-! ## Conversion tests -/

#eval do
  assert! Ordering.lt.toWeak == WeakOrdering.lt
  assert! Ordering.eq.toWeak == WeakOrdering.equivalent
  assert! Ordering.gt.toWeak == WeakOrdering.gt

#eval do
  assert! Ordering.lt.toPartial == PartialOrdering.lt
  assert! Ordering.eq.toPartial == PartialOrdering.equivalent
  assert! Ordering.gt.toPartial == PartialOrdering.gt

#eval do
  assert! WeakOrdering.lt.toPartial == PartialOrdering.lt
  assert! WeakOrdering.equivalent.toPartial == PartialOrdering.equivalent
  assert! WeakOrdering.gt.toPartial == PartialOrdering.gt

/-! ## Named comparison functions -/

#eval do
  assert! Ordering.eq.is_eq == true
  assert! Ordering.lt.is_eq == false
  assert! Ordering.gt.is_eq == false
  assert! Ordering.lt.is_lt == true
  assert! Ordering.gt.is_gt == true
  assert! Ordering.lt.is_lteq == true
  assert! Ordering.eq.is_lteq == true
  assert! Ordering.gt.is_lteq == false
  assert! Ordering.gt.is_gteq == true
  assert! Ordering.eq.is_gteq == true
  assert! Ordering.lt.is_gteq == false

/-! ## PartialOrdering has unordered -/

#eval do
  assert! PartialOrdering.unordered != PartialOrdering.lt
  assert! PartialOrdering.unordered != PartialOrdering.equivalent
  assert! PartialOrdering.unordered != PartialOrdering.gt
  assert! PartialOrdering.unordered.is_eq == false
  assert! PartialOrdering.unordered.is_lt == false
  assert! PartialOrdering.unordered.is_gt == false
  assert! PartialOrdering.unordered.is_lteq == false
  assert! PartialOrdering.unordered.is_gteq == false

/-! ## Nat StrongOrd tests -/

#eval do
  assert! StrongOrd.strongCmp 0 0 == Ordering.eq
  assert! StrongOrd.strongCmp 1 2 == Ordering.lt
  assert! StrongOrd.strongCmp 2 1 == Ordering.gt
  assert! StrongOrd.strongCmp 5 5 == Ordering.eq
  assert! StrongOrd.strongCmp 0 100 == Ordering.lt
  assert! StrongOrd.strongCmp 100 0 == Ordering.gt

/-! ## Nat StrongOrd flip test -/

#eval do
  -- For all pairs in a small range, flip is consistent
  for a in List.range 10 do
    for b in List.range 10 do
      let ab := StrongOrd.strongCmp a b
      let ba := StrongOrd.strongCmp b a
      assert! ab.flip == ba

/-! ## Nat StrongOrd transitivity test -/

#eval do
  -- Test lt transitivity for small values
  for a in List.range 8 do
    for b in List.range 8 do
      for c in List.range 8 do
        let ab := StrongOrd.strongCmp a b
        let bc := StrongOrd.strongCmp b c
        let ac := StrongOrd.strongCmp a c
        if ab == Ordering.lt && bc == Ordering.lt then
          assert! ac == Ordering.lt

/-! ## Int StrongOrd tests -/

#eval do
  assert! StrongOrd.strongCmp (0 : Int) 0 == Ordering.eq
  assert! StrongOrd.strongCmp (1 : Int) 2 == Ordering.lt
  assert! StrongOrd.strongCmp (2 : Int) 1 == Ordering.gt
  assert! StrongOrd.strongCmp (-5 : Int) 5 == Ordering.lt
  assert! StrongOrd.strongCmp (5 : Int) (-5) == Ordering.gt
  assert! StrongOrd.strongCmp (-3 : Int) (-3) == Ordering.eq
  assert! StrongOrd.strongCmp (-3 : Int) (-1) == Ordering.lt
  assert! StrongOrd.strongCmp (-1 : Int) (-3) == Ordering.gt

/-! ## Pair lexicographic StrongOrd tests -/

#eval do
  let p1 := Pair.make 1 2
  let p2 := Pair.make 1 3
  let p3 := Pair.make 2 1
  let p4 := Pair.make 1 2
  -- Same pair is eq
  assert! StrongOrd.strongCmp p1 p4 == Ordering.eq
  -- Same first, different second
  assert! StrongOrd.strongCmp p1 p2 == Ordering.lt
  assert! StrongOrd.strongCmp p2 p1 == Ordering.gt
  -- Different first dominates
  assert! StrongOrd.strongCmp p1 p3 == Ordering.lt
  assert! StrongOrd.strongCmp p3 p1 == Ordering.gt

#eval do
  -- Pair reflexivity
  let p := Pair.make 42 99
  assert! StrongOrd.strongCmp p p == Ordering.eq

#eval do
  -- Pair flip consistency
  let pairs := [Pair.make 1 2, Pair.make 1 3, Pair.make 2 1, Pair.make 2 2]
  for p in pairs do
    for q in pairs do
      let pq := StrongOrd.strongCmp p q
      let qp := StrongOrd.strongCmp q p
      assert! pq.flip == qp

#eval do
  -- Pair transitivity
  let pairs := [Pair.make 1 1, Pair.make 1 2, Pair.make 2 1, Pair.make 2 2]
  for p in pairs do
    for q in pairs do
      for r in pairs do
        let pq := StrongOrd.strongCmp p q
        let qr := StrongOrd.strongCmp q r
        let pr := StrongOrd.strongCmp p r
        if pq == Ordering.lt && qr == Ordering.lt then
          assert! pr == Ordering.lt

/-! ## Nested pair tests (Pair (Pair Nat Nat) Nat) -/

#eval do
  let p1 := Pair.make (Pair.make 1 2) 10
  let p2 := Pair.make (Pair.make 1 3) 5
  let p3 := Pair.make (Pair.make 1 2) 10
  assert! StrongOrd.strongCmp p1 p3 == Ordering.eq
  assert! StrongOrd.strongCmp p1 p2 == Ordering.lt
  assert! StrongOrd.strongCmp p2 p1 == Ordering.gt

end Cpp.Ordering.Tests

/-! ## Named test defs for TestedConjectures -/

namespace Cpp

Test strongCmp_refl_nat :=
  show StrongOrd.strongCmp 42 42 = Ordering.eq from rfl

Test strongCmp_flip_nat :=
  show (StrongOrd.strongCmp 3 7).flip = StrongOrd.strongCmp 7 3 from rfl

Test strongCmp_lt_trans_nat :=
  show StrongOrd.strongCmp 1 3 = Ordering.lt from rfl

Test strongCmp_refl_int :=
  show StrongOrd.strongCmp (-5 : Int) (-5) = Ordering.eq from rfl

Test strongCmp_flip_int :=
  show (StrongOrd.strongCmp (1 : Int) (2 : Int)).flip = StrongOrd.strongCmp 2 1 from rfl

Test strongCmp_refl_pair :=
  show StrongOrd.strongCmp (Pair.make 1 2) (Pair.make 1 2) = Ordering.eq from rfl

Test strongCmp_flip_pair :=
  show (StrongOrd.strongCmp (Pair.make 1 2) (Pair.make 1 3)).flip =
       StrongOrd.strongCmp (Pair.make 1 3) (Pair.make 1 2) from rfl

Test strongCmp_lt_trans_pair :=
  show StrongOrd.strongCmp (Pair.make 1 2) (Pair.make 2 1) = Ordering.lt from rfl

Test flip_involution :=
  show Ordering.lt.flip.flip = Ordering.lt from rfl

Test toWeak_preserves :=
  show Ordering.lt.toWeak = WeakOrdering.lt from rfl

Test toPartial_preserves :=
  show Ordering.lt.toPartial = PartialOrdering.lt from rfl

end Cpp
