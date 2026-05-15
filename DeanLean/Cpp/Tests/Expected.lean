import DeanLean.Basic
import DeanLean.Cpp.Code.Expected

namespace Cpp.Expected.Tests

-- Basic construction and observers
#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 42
  assert! x.has_value == true
  assert! x.value == 42
  assert! x.value_or 0 == 42

#eval do
  let x : Cpp.Expected String Nat := Cpp.Expected.unexpected "error"
  assert! x.has_value == false
  assert! x.error == "error"
  assert! x.value_or 99 == 99

-- transform
#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 10
  let doubled := x.transform (· * 2)
  assert! doubled.has_value == true
  assert! doubled.value == 20

#eval do
  let x : Cpp.Expected String Nat := Cpp.Expected.unexpected "fail"
  assert! (x.transform (· * 2)).has_value == false

-- transform_error
#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 10
  let y := x.transform_error (· ++ "!")
  assert! y.has_value == true
  assert! y.value == 10

#eval do
  let x : Cpp.Expected String Nat := Cpp.Expected.unexpected "fail"
  let y := x.transform_error (· ++ "!")
  assert! y.has_value == false
  assert! y.error == "fail!"

-- and_then
#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 5
  let result := x.and_then fun n =>
    if n > 3 then Cpp.Expected.ok (n * 10) else Cpp.Expected.unexpected "too small"
  assert! result.value == 50

#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 2
  let result := x.and_then fun n =>
    if n > 3 then Cpp.Expected.ok (n * 10) else Cpp.Expected.unexpected "too small"
  assert! result.has_value == false

#eval do
  let x : Cpp.Expected String Nat := Cpp.Expected.unexpected "error"
  let result := x.and_then fun n => Cpp.Expected.ok (n + 1)
  assert! result.has_value == false

-- or_else
#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 7
  let result := x.or_else fun _ => Cpp.Expected.ok (E := Nat) (T := Nat) 42
  assert! result.value == 7

#eval do
  let x : Cpp.Expected String Nat := Cpp.Expected.unexpected "error"
  let result := x.or_else fun e => Cpp.Expected.ok (E := Nat) (T := Nat) e.length
  assert! result.value == 5

-- Monadic do-notation
#eval do
  let result : Cpp.Expected String Nat := do
    let a ← Cpp.Expected.ok 10
    let b ← Cpp.Expected.ok 20
    pure (a + b)
  assert! result == Cpp.Expected.ok 30

#eval do
  let result : Cpp.Expected String Nat := do
    let a ← Cpp.Expected.ok 10
    let _ ← (Cpp.Expected.unexpected "oops" : Cpp.Expected String Nat)
    pure (a + 20)
  assert! result == Cpp.Expected.unexpected "oops"

-- Roundtrip conversions
#eval do
  let x := Cpp.Expected.ok (E := String) (T := Nat) 42
  let y := Cpp.Expected.ofExcept x.toExcept
  assert! y == x

#eval do
  let x : Cpp.Expected String Nat := Cpp.Expected.unexpected "err"
  let y := Cpp.Expected.ofExcept x.toExcept
  assert! y == x

#eval do
  let x : Except String Nat := Except.ok 42
  let y := Cpp.Expected.ofExcept x
  let z := y.toExcept
  assert! z matches Except.ok 42

#eval do
  let x : Except String Nat := Except.error "err"
  let y := Cpp.Expected.ofExcept x
  let z := y.toExcept
  assert! z matches Except.error "err"

end Cpp.Expected.Tests

namespace Cpp.Expected

-- Monad law test witnesses

Test monad_left_identity :=
  show (pure 5 : Expected String Nat) >>= Expected.ok = Expected.ok 5 from rfl

Test monad_right_identity :=
  show (Expected.ok 5 : Expected String Nat) >>= (pure · : Nat → Expected String Nat) = Expected.ok 5 from rfl

Test monad_associativity :=
  show ((Expected.ok 3 : Expected String Nat) >>= (fun n => Expected.ok (n + 1))) >>= (fun n => Expected.ok (n * 2))
    = (Expected.ok 3 : Expected String Nat) >>= (fun n => (fun n => Expected.ok (n + 1)) n >>= (fun n => Expected.ok (n * 2))) from rfl

-- Functor law test witnesses

Test transform_compose :=
  show ((Expected.ok 3 : Expected String Nat).transform (· + 1)).transform (· * 2)
    = (Expected.ok 3 : Expected String Nat).transform ((· * 2) ∘ (· + 1)) from rfl

Test transform_id :=
  show (Expected.ok 5 : Expected String Nat).transform id = Expected.ok 5 from rfl

-- or_else / and_then interaction test witness

Test or_else_and_then_unexpected :=
  show ((Expected.unexpected "e" : Expected String Nat).or_else (fun _ => Expected.ok 5)).and_then (fun n => Expected.ok (n + 1))
    = ((fun _ => Expected.ok (E := String) (T := Nat) 5) "e").and_then (fun n => Expected.ok (n + 1)) from rfl

end Cpp.Expected
