import DeanLean.Basic

namespace Cpp

/-! # C++ Concepts Library (N4950 §18)

  Formalizes the C++ <concepts> header as Lean typeclasses.
  §18.4  Language-related concepts
  §18.5  Comparison concepts
  §18.6  Object concepts
  §18.7  Callable concepts
-/

-- ============================================================================
-- §18.4.2 same_as
-- ============================================================================

/-- `same_as T U` holds when T and U are the same type (§18.4.2). -/
def same_as (T U : Type) : Prop := T = U

-- ============================================================================
-- §18.4.4 convertible_to
-- ============================================================================

/-- `ConvertibleTo T U` means there exists a coercion from T to U (§18.4.4). -/
class ConvertibleTo (T U : Type) where
  convert : T → U

-- ============================================================================
-- §18.4.3 derived_from
-- ============================================================================

/-- `DerivedFrom D B` models that D is derived from B, i.e., D can be converted to B (§18.4.3).
    In Lean we model this as the existence of a coercion from D to B. -/
class DerivedFrom (D B : Type) extends ConvertibleTo D B

-- ============================================================================
-- §18.4.7 Arithmetic concepts
-- ============================================================================

/-- `Integral T` marks T as an integral type (§18.4.7). -/
class Integral (T : Type) where
  toInt : T → Int

/-- `SignedIntegral T` marks T as a signed integral type (§18.4.7).
    Refines `Integral`. -/
class SignedIntegral (T : Type) extends Integral T where
  is_signed : ∀ (_ : T), true = true  -- marker field

/-- `UnsignedIntegral T` marks T as an unsigned integral type (§18.4.7).
    Refines `Integral`. -/
class UnsignedIntegral (T : Type) extends Integral T where
  toNat : T → Nat

/-- `FloatingPoint T` marks T as a floating-point type (§18.4.7). -/
class FloatingPoint (T : Type) where
  toFloat : T → Float

-- ============================================================================
-- §18.4.8 assignable_from
-- ============================================================================

/-- `AssignableFrom T U` means a value of type U can be assigned into type T (§18.4.8). -/
class AssignableFrom (T U : Type) where
  assign : T → U → T

-- ============================================================================
-- §18.4.10 destructible / §18.4.12 default_initializable
-- ============================================================================

/-- `Destructible T` means T can be destroyed; trivially true for all Lean types (§18.4.10). -/
class Destructible (T : Type) where
  destruct : T → Unit := fun _ => ()

/-- `DefaultInitializable T` means T has a default value (§18.4.12). -/
class DefaultInitializable (T : Type) where
  defaultValue : T

instance {T : Type} [Inhabited T] : DefaultInitializable T where
  defaultValue := default

-- ============================================================================
-- §18.4.13 move_constructible / §18.4.14 copy_constructible
-- ============================================================================

/-- `MoveConstructible T` means T supports move construction (§18.4.13).
    In Lean all types are trivially movable. -/
class MoveConstructible (T : Type) extends Destructible T where
  move : T → T := fun x => x

/-- `CopyConstructible T` means T supports copy construction (§18.4.14).
    Refines `MoveConstructible`. -/
class CopyConstructible (T : Type) extends MoveConstructible T where
  copy : T → T := fun x => x

-- ============================================================================
-- §18.5.4 equality_comparable
-- ============================================================================

/-- `EqualityComparable T` provides `==` and requires it to be an equivalence relation (§18.5.4).
    We use `DecidableEq` as the Lean analog. -/
class EqualityComparable (T : Type) where
  eq_decidable : DecidableEq T
  eq_refl  : ∀ (a : T), a = a
  eq_symm  : ∀ (a b : T), a = b → b = a
  eq_trans : ∀ (a b c : T), a = b → b = c → a = c

instance {T : Type} [DecidableEq T] : EqualityComparable T where
  eq_decidable := inferInstance
  eq_refl  := fun a => Eq.refl a
  eq_symm  := fun _ _ h => h.symm
  eq_trans := fun _ _ _ h1 h2 => h1.trans h2

-- ============================================================================
-- §18.5.5 totally_ordered
-- ============================================================================

/-- `TotallyOrdered T` requires a total order with `<`, `≤` obeying standard laws (§18.5.5).
    Refines `EqualityComparable`. -/
class TotallyOrdered (T : Type) extends EqualityComparable T where
  le : T → T → Prop
  lt : T → T → Prop
  le_refl       : ∀ (a : T), le a a
  le_antisymm   : ∀ (a b : T), le a b → le b a → a = b
  le_trans      : ∀ (a b c : T), le a b → le b c → le a c
  le_total      : ∀ (a b : T), le a b ∨ le b a
  lt_iff_le_ne  : ∀ (a b : T), lt a b ↔ (le a b ∧ a ≠ b)

-- ============================================================================
-- §18.6 Object concepts
-- ============================================================================

/-- `Semiregular T` is `CopyConstructible` + `DefaultInitializable` (§18.6). -/
class Semiregular (T : Type) extends CopyConstructible T, DefaultInitializable T

/-- `Regular T` is `Semiregular` + `EqualityComparable` (§18.6). -/
class Regular (T : Type) extends Semiregular T, EqualityComparable T

-- ============================================================================
-- §18.7 Callable concepts
-- ============================================================================

/-- `Invocable F T U` means F is a callable from T to U (§18.7). -/
class Invocable (F T U : Type) where
  invoke : F → T → U

/-- `RegularInvocable F T U` refines `Invocable`; the function must be equality-preserving
    (§18.7). -/
class RegularInvocable (F T U : Type) extends Invocable F T U

/-- `Predicate F T` is an invocable returning Bool (§18.7). -/
class Predicate (F T : Type) extends Invocable F T Bool

/-- `Relation F T U` is a predicate on two arguments (§18.7). -/
class Relation (F T U : Type) where
  relate : F → T → U → Bool

-- ============================================================================
-- Instances for built-in types
-- ============================================================================

-- Integral instances
instance : Integral Int where
  toInt := id

instance : SignedIntegral Int where
  is_signed := fun _ => rfl

instance : Integral Nat where
  toInt := Int.ofNat

instance : UnsignedIntegral Nat where
  toNat := id

instance : Integral UInt8 where
  toInt := fun n => Int.ofNat n.toNat

instance : UnsignedIntegral UInt8 where
  toNat := UInt8.toNat

instance : Integral UInt16 where
  toInt := fun n => Int.ofNat n.toNat

instance : UnsignedIntegral UInt16 where
  toNat := UInt16.toNat

instance : Integral UInt32 where
  toInt := fun n => Int.ofNat n.toNat

instance : UnsignedIntegral UInt32 where
  toNat := UInt32.toNat

instance : Integral UInt64 where
  toInt := fun n => Int.ofNat n.toNat

instance : UnsignedIntegral UInt64 where
  toNat := UInt64.toNat

-- FloatingPoint instance
instance : FloatingPoint Float where
  toFloat := id

-- ConvertibleTo: natural coercions
instance : ConvertibleTo Nat Int where
  convert := Int.ofNat

-- Function types are Invocable
instance {T U : Type} : Invocable (T → U) T U where
  invoke := fun f x => f x

-- ============================================================================
-- Relationship helpers (definitions that proofs will use)
-- ============================================================================

/-- `same_as` is symmetric. -/
def same_as_symm {T U : Type} (h : same_as T U) : same_as U T :=
  h.symm

/-- `signed_integral` implies `integral` — accessor for the proof. -/
def signed_integral_is_integral (T : Type) [SignedIntegral T] : Integral T :=
  inferInstance

/-- `unsigned_integral` implies `integral` — accessor for the proof. -/
def unsigned_integral_is_integral (T : Type) [UnsignedIntegral T] : Integral T :=
  inferInstance

/-- `regular` implies `semiregular`. -/
def regular_is_semiregular (T : Type) [Regular T] : Semiregular T :=
  inferInstance

/-- `totally_ordered` implies `equality_comparable`. -/
def totally_ordered_is_equality_comparable (T : Type) [TotallyOrdered T] : EqualityComparable T :=
  inferInstance

/-- `signed_integral` and `unsigned_integral` are disjoint — they cannot both hold
    for the same type (a type is either signed or unsigned, not both).
    We model this as a Prop that the user can assert. -/
def signed_unsigned_disjoint_stmt : Prop :=
  ∀ (T : Type), SignedIntegral T → UnsignedIntegral T → False

end Cpp
