import DeanLean.Basic

namespace Cpp

inductive Optional (T : Type) where
  | nullopt : Optional T
  | some (val : T) : Optional T
deriving Repr, BEq, Inhabited

namespace Optional

variable {T U : Type}

def has_value : Optional T → Bool
  | nullopt => false
  | some _  => true

def value [Inhabited T] : Optional T → T
  | some v  => v
  | nullopt => panic! "bad_optional_access"

def value_or (o : Optional T) (default : T) : T :=
  match o with
  | some v  => v
  | nullopt => default

def emplace (_ : Optional T) (v : T) : Optional T := some v

def reset (_ : Optional T) : Optional T := nullopt

def and_then (o : Optional T) (f : T → Optional U) : Optional U :=
  match o with
  | some v  => f v
  | nullopt => nullopt

def transform (o : Optional T) (f : T → U) : Optional U :=
  match o with
  | some v  => some (f v)
  | nullopt => nullopt

def or_else (o : Optional T) (f : Unit → Optional T) : Optional T :=
  match o with
  | some v  => some v
  | nullopt => f ()

instance : Monad Optional where
  pure := some
  bind := and_then

instance [BEq T] : BEq (Optional T) where
  beq
    | some a, some b => a == b
    | nullopt, nullopt => true
    | _, _ => false

instance [Ord T] : Ord (Optional T) where
  compare
    | nullopt, nullopt => .eq
    | nullopt, some _  => .lt
    | some _,  nullopt => .gt
    | some a,  some b  => compare a b

def make_optional (v : T) : Optional T := some v

def toOption : Optional T → Option T
  | some v  => Option.some v
  | nullopt => Option.none

def ofOption : Option T → Optional T
  | Option.some v => some v
  | Option.none   => nullopt

end Optional

end Cpp
