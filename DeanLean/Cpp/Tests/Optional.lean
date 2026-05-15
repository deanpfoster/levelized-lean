import DeanLean.Basic
import DeanLean.Cpp.Code.Optional

namespace Cpp.Optional.Tests

#eval do
  let o := Cpp.Optional.some 42
  assert! o.has_value == true
  assert! o.value == 42
  assert! o.value_or 0 == 42

#eval do
  let o : Cpp.Optional Nat := Cpp.Optional.nullopt
  assert! o.has_value == false
  assert! o.value_or 99 == 99

#eval do
  let o := Cpp.Optional.some 10
  let doubled := o.transform (· * 2)
  assert! doubled.has_value == true
  assert! doubled.value == 20

#eval do
  let o : Cpp.Optional Nat := Cpp.Optional.nullopt
  assert! (o.transform (· * 2)).has_value == false

#eval do
  let o := Cpp.Optional.some 5
  let result := o.and_then fun n =>
    if n > 3 then Cpp.Optional.some (n * 10) else Cpp.Optional.nullopt
  assert! result.value == 50

#eval do
  let o := Cpp.Optional.some 2
  let result := o.and_then fun n =>
    if n > 3 then Cpp.Optional.some (n * 10) else Cpp.Optional.nullopt
  assert! result.has_value == false

#eval do
  let o : Cpp.Optional Nat := Cpp.Optional.nullopt
  let result := o.or_else fun () => Cpp.Optional.some 42
  assert! result.value == 42

#eval do
  let o := Cpp.Optional.some 7
  let result := o.or_else fun () => Cpp.Optional.some 42
  assert! result.value == 7

#eval do
  let result := do
    let a ← Cpp.Optional.some 10
    let b ← Cpp.Optional.some 20
    pure (a + b)
  assert! result == Cpp.Optional.some 30

#eval do
  let result : Cpp.Optional Nat := do
    let a ← Cpp.Optional.some 10
    let _ ← (Cpp.Optional.nullopt : Cpp.Optional Nat)
    pure (a + 20)
  assert! result == Cpp.Optional.nullopt

end Cpp.Optional.Tests

namespace Cpp.Optional

Test monad_left_identity :=
  show (pure 5 : Optional Nat) >>= Optional.some = Optional.some 5 from rfl

Test monad_right_identity :=
  show (Optional.some 5) >>= (pure · : Nat → Optional Nat) = Optional.some 5 from rfl

Test monad_associativity :=
  show ((Optional.some 3) >>= (fun n => Optional.some (n + 1))) >>= (fun n => Optional.some (n * 2))
    = (Optional.some 3) >>= (fun n => (fun n => Optional.some (n + 1)) n >>= (fun n => Optional.some (n * 2))) from rfl

Test transform_compose :=
  show ((Optional.some 3).transform (· + 1)).transform (· * 2)
    = (Optional.some 3).transform ((· * 2) ∘ (· + 1)) from rfl

Test transform_id :=
  show (Optional.some 5).transform id = Optional.some 5 from rfl

Test or_else_and_then_nullopt :=
  show ((Optional.nullopt : Optional Nat).or_else (fun () => Optional.some 5)).and_then (fun n => Optional.some (n + 1))
    = ((fun () => Optional.some 5) ()).and_then (fun n => Optional.some (n + 1)) from rfl

end Cpp.Optional
