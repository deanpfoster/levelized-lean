import DeanLean.Basic

namespace Cpp

/-! # C++ numeric_limits (N4950 §17.3.5) and integer comparison (§22.2.7)

  Formalizes `numeric_limits` as a typeclass for Lean's fixed-width integer types,
  plus safe integer comparison functions `cmp_equal`, `cmp_less`, `cmp_greater`,
  and `in_range` from `<utility>`.
-/

/-- C++ `float_round_style` enumeration (§17.3.4) -/
inductive FloatRoundStyle where
  | round_indeterminate
  | round_toward_zero
  | round_to_nearest
  | round_toward_infinity
  | round_toward_neg_infinity
deriving Repr, BEq, DecidableEq, Inhabited

/-- C++ `numeric_limits` class template (§17.3.5).
    We focus on the integer-relevant fields.
    For integer types: min, max, digits (non-sign bits), digits10,
    is_signed, is_integer, is_exact, is_bounded, is_modulo, radix. -/
class NumericLimits (T : Type) where
  /-- Minimum finite value -/
  min : T
  /-- Maximum finite value -/
  max : T
  /-- Lowest finite value (for integers, same as min) -/
  lowest : T
  /-- Number of radix digits (non-sign bits for integers) -/
  digits : Nat
  /-- Number of base-10 digits representable without change -/
  digits10 : Nat
  /-- True if signed type -/
  is_signed : Bool
  /-- True if integer type -/
  is_integer : Bool
  /-- True if exact representation -/
  is_exact : Bool
  /-- Base of the representation -/
  radix : Nat
  /-- True if bounded -/
  is_bounded : Bool
  /-- True if modulo arithmetic -/
  is_modulo : Bool
  /-- Rounding style (round_toward_zero for integers) -/
  round_style : FloatRoundStyle

namespace NumericLimits

/-- Convert min to a natural number for comparison purposes -/
def minNat (T : Type) [NumericLimits T] [BEq T] [ToString T] : Nat := 0

end NumericLimits

/-! ## Instances for unsigned types -/

instance : NumericLimits UInt8 where
  min := 0
  max := 255
  lowest := 0
  digits := 8
  digits10 := 2    -- floor(8 * log10(2)) = 2
  is_signed := false
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := true
  round_style := .round_toward_zero

instance : NumericLimits UInt16 where
  min := 0
  max := 65535
  lowest := 0
  digits := 16
  digits10 := 4    -- floor(16 * log10(2)) = 4
  is_signed := false
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := true
  round_style := .round_toward_zero

instance : NumericLimits UInt32 where
  min := 0
  max := 4294967295
  lowest := 0
  digits := 32
  digits10 := 9    -- floor(32 * log10(2)) = 9
  is_signed := false
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := true
  round_style := .round_toward_zero

instance : NumericLimits UInt64 where
  min := 0
  max := 18446744073709551615
  lowest := 0
  digits := 64
  digits10 := 19   -- floor(64 * log10(2)) = floor(19.265) = 19
  is_signed := false
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := true
  round_style := .round_toward_zero

/-! ## Instances for signed types

  Lean 4 does not have built-in Int8/Int16/Int32/Int64 types in the same way
  as the unsigned variants. We define them as wrappers. -/

/-- Signed 8-bit integer, two's complement, range [-128, 127] -/
structure Int8 where
  val : Int
  valid : -128 ≤ val ∧ val ≤ 127
deriving Repr, DecidableEq

/-- Signed 16-bit integer, two's complement, range [-32768, 32767] -/
structure Int16 where
  val : Int
  valid : -32768 ≤ val ∧ val ≤ 32767
deriving Repr, DecidableEq

/-- Signed 32-bit integer, two's complement, range [-2147483648, 2147483647] -/
structure Int32 where
  val : Int
  valid : -2147483648 ≤ val ∧ val ≤ 2147483647
deriving Repr, DecidableEq

/-- Signed 64-bit integer, two's complement -/
structure Int64 where
  val : Int
  valid : -9223372036854775808 ≤ val ∧ val ≤ 9223372036854775807
deriving Repr, DecidableEq

namespace Int8
def mk' (n : Int) (h1 : -128 ≤ n := by omega) (h2 : n ≤ 127 := by omega) : Int8 :=
  ⟨n, ⟨h1, h2⟩⟩
instance : BEq Int8 where beq a b := a.val == b.val
instance : LE Int8 where le a b := a.val ≤ b.val
instance : LT Int8 where lt a b := a.val < b.val
instance : Inhabited Int8 where default := ⟨0, by omega⟩
instance : ToString Int8 where toString a := toString a.val
end Int8

namespace Int16
def mk' (n : Int) (h1 : -32768 ≤ n := by omega) (h2 : n ≤ 32767 := by omega) : Int16 :=
  ⟨n, ⟨h1, h2⟩⟩
instance : BEq Int16 where beq a b := a.val == b.val
instance : LE Int16 where le a b := a.val ≤ b.val
instance : LT Int16 where lt a b := a.val < b.val
instance : Inhabited Int16 where default := ⟨0, by omega⟩
instance : ToString Int16 where toString a := toString a.val
end Int16

namespace Int32
def mk' (n : Int) (h1 : -2147483648 ≤ n := by omega) (h2 : n ≤ 2147483647 := by omega) : Int32 :=
  ⟨n, ⟨h1, h2⟩⟩
instance : BEq Int32 where beq a b := a.val == b.val
instance : LE Int32 where le a b := a.val ≤ b.val
instance : LT Int32 where lt a b := a.val < b.val
instance : Inhabited Int32 where default := ⟨0, by omega⟩
instance : ToString Int32 where toString a := toString a.val
end Int32

namespace Int64
def mk' (n : Int) (h1 : -9223372036854775808 ≤ n := by omega)
    (h2 : n ≤ 9223372036854775807 := by omega) : Int64 :=
  ⟨n, ⟨h1, h2⟩⟩
instance : BEq Int64 where beq a b := a.val == b.val
instance : LE Int64 where le a b := a.val ≤ b.val
instance : LT Int64 where lt a b := a.val < b.val
instance : Inhabited Int64 where default := ⟨0, by omega⟩
instance : ToString Int64 where toString a := toString a.val
end Int64

instance : NumericLimits Int8 where
  min := ⟨-128, by omega⟩
  max := ⟨127, by omega⟩
  lowest := ⟨-128, by omega⟩
  digits := 7       -- non-sign bits
  digits10 := 2     -- floor(7 * log10(2)) = 2
  is_signed := true
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := false  -- signed overflow is UB in C++
  round_style := .round_toward_zero

instance : NumericLimits Int16 where
  min := ⟨-32768, by omega⟩
  max := ⟨32767, by omega⟩
  lowest := ⟨-32768, by omega⟩
  digits := 15
  digits10 := 4     -- floor(15 * log10(2)) = 4
  is_signed := true
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := false
  round_style := .round_toward_zero

instance : NumericLimits Int32 where
  min := ⟨-2147483648, by omega⟩
  max := ⟨2147483647, by omega⟩
  lowest := ⟨-2147483648, by omega⟩
  digits := 31
  digits10 := 9     -- floor(31 * log10(2)) = 9
  is_signed := true
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := false
  round_style := .round_toward_zero

instance : NumericLimits Int64 where
  min := ⟨-9223372036854775808, by omega⟩
  max := ⟨9223372036854775807, by omega⟩
  lowest := ⟨-9223372036854775808, by omega⟩
  digits := 63
  digits10 := 18    -- floor(63 * log10(2)) = 18
  is_signed := true
  is_integer := true
  is_exact := true
  radix := 2
  is_bounded := true
  is_modulo := false
  round_style := .round_toward_zero

/-! ## Integer comparison functions (N4950 §22.2.7)

  These functions safely compare integers that may have different signedness.
  They work by promoting both values to Int for comparison.
-/

/-- Typeclass for types that can be safely promoted to Int for comparison -/
class IntPromotable (T : Type) where
  toInt : T → Int

instance : IntPromotable UInt8 where toInt n := (n.toNat : Int)
instance : IntPromotable UInt16 where toInt n := (n.toNat : Int)
instance : IntPromotable UInt32 where toInt n := (n.toNat : Int)
instance : IntPromotable UInt64 where toInt n := (n.toNat : Int)
instance : IntPromotable Int8 where toInt n := n.val
instance : IntPromotable Int16 where toInt n := n.val
instance : IntPromotable Int32 where toInt n := n.val
instance : IntPromotable Int64 where toInt n := n.val

/-- `cmp_equal(t, u)` — safe equality comparison across signed/unsigned (§22.2.7) -/
def cmp_equal {T U : Type} [IntPromotable T] [IntPromotable U] (t : T) (u : U) : Bool :=
  IntPromotable.toInt t == IntPromotable.toInt u

/-- `cmp_less(t, u)` — safe less-than comparison across signed/unsigned (§22.2.7) -/
def cmp_less {T U : Type} [IntPromotable T] [IntPromotable U] (t : T) (u : U) : Bool :=
  IntPromotable.toInt t < IntPromotable.toInt u

/-- `cmp_greater(t, u)` — safe greater-than comparison across signed/unsigned (§22.2.7) -/
def cmp_greater {T U : Type} [IntPromotable T] [IntPromotable U] (t : T) (u : U) : Bool :=
  cmp_less u t

/-- `in_range<R>(t)` — checks if t is representable as R (§22.2.7) -/
def in_range (R : Type) {T : Type} [NumericLimits R] [IntPromotable R] [IntPromotable T]
    (t : T) : Bool :=
  let tVal := IntPromotable.toInt t
  let rMin := IntPromotable.toInt (NumericLimits.min : R)
  let rMax := IntPromotable.toInt (NumericLimits.max : R)
  rMin ≤ tVal && tVal ≤ rMax

/-! ## Properties expressed as Prop (for proofs) -/

/-- `min ≤ max` for NumericLimits, expressed via IntPromotable -/
def NumericLimits.min_le_max_prop (T : Type) [NumericLimits T] [IntPromotable T] : Prop :=
  IntPromotable.toInt (NumericLimits.min : T) ≤ IntPromotable.toInt (NumericLimits.max : T)

/-- `digits > 0` for NumericLimits -/
def NumericLimits.digits_pos_prop (T : Type) [NumericLimits T] : Prop :=
  NumericLimits.digits (self := ‹NumericLimits T›) > 0

/-- `is_signed` correctness: signed types have min < 0 (via Int promotion) -/
def NumericLimits.is_signed_correct_prop (T : Type) [NumericLimits T] [IntPromotable T] : Prop :=
  NumericLimits.is_signed (self := ‹NumericLimits T›) = true →
    IntPromotable.toInt (NumericLimits.min : T) < 0

/-- `is_signed` correctness for unsigned: unsigned types have min >= 0 -/
def NumericLimits.unsigned_min_nonneg_prop (T : Type) [NumericLimits T] [IntPromotable T] : Prop :=
  NumericLimits.is_signed (self := ‹NumericLimits T›) = false →
    IntPromotable.toInt (NumericLimits.min : T) ≥ 0

/-- `cmp_equal` correctness: equal iff same integer value -/
def cmp_equal_correct_prop {T U : Type} [IntPromotable T] [IntPromotable U]
    (t : T) (u : U) : Prop :=
  cmp_equal t u = true ↔ IntPromotable.toInt t = IntPromotable.toInt u

/-- `cmp_less` correctness: less iff strictly less integer value -/
def cmp_less_correct_prop {T U : Type} [IntPromotable T] [IntPromotable U]
    (t : T) (u : U) : Prop :=
  cmp_less t u = true ↔ IntPromotable.toInt t < IntPromotable.toInt u

/-- `cmp_greater` is the flip of `cmp_less` -/
def cmp_greater_flip_prop {T U : Type} [IntPromotable T] [IntPromotable U]
    (t : T) (u : U) : Prop :=
  cmp_greater t u = cmp_less u t

end Cpp
