import DeanLean.Basic

namespace Cpp

/-- C++ std::expected<T,E> — holds either a value of type T (ok) or an error of type E (unexpected).
    Type parameters are ordered (E, T) to match Lean's Except and enable Monad instance. -/
inductive Expected (E : Type) (T : Type) where
  | ok (val : T) : Expected E T
  | unexpected (err : E) : Expected E T
deriving Repr, BEq, Inhabited

namespace Expected

variable {T U E E2 : Type}

def has_value : Expected E T → Bool
  | ok _        => true
  | unexpected _ => false

def value [Inhabited T] : Expected E T → T
  | ok v        => v
  | unexpected _ => panic! "bad_expected_access"

def error [Inhabited E] : Expected E T → E
  | unexpected e => e
  | ok _         => panic! "bad_expected_access: has value"

def value_or (x : Expected E T) (default : T) : T :=
  match x with
  | ok v        => v
  | unexpected _ => default

def and_then (x : Expected E T) (f : T → Expected E U) : Expected E U :=
  match x with
  | ok v        => f v
  | unexpected e => unexpected e

def transform (x : Expected E T) (f : T → U) : Expected E U :=
  match x with
  | ok v        => ok (f v)
  | unexpected e => unexpected e

def transform_error (x : Expected E T) (f : E → E2) : Expected E2 T :=
  match x with
  | ok v        => ok v
  | unexpected e => unexpected (f e)

def or_else (x : Expected E T) (f : E → Expected E2 T) : Expected E2 T :=
  match x with
  | ok v        => ok v
  | unexpected e => f e

instance : Monad (Expected E) where
  pure := ok
  bind := and_then

instance [BEq T] [BEq E] : BEq (Expected E T) where
  beq
    | ok a, ok b             => a == b
    | unexpected a, unexpected b => a == b
    | _, _                   => false

def toExcept : Expected E T → Except E T
  | ok v        => Except.ok v
  | unexpected e => Except.error e

def ofExcept : Except E T → Expected E T
  | Except.ok v    => ok v
  | Except.error e => unexpected e

end Expected

end Cpp
