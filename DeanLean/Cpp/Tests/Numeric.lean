import DeanLean.Basic
import DeanLean.Cpp.Code.Numeric

namespace Cpp.Numeric.Tests

/-! ## numeric_limits field tests -/

-- UInt8
#eval do
  assert! (NumericLimits.min : UInt8) == 0
  assert! (NumericLimits.max : UInt8) == 255
  assert! (NumericLimits.digits (self := instNumericLimitsUInt8)) == 8
  assert! (NumericLimits.is_signed (self := instNumericLimitsUInt8)) == false
  assert! (NumericLimits.is_integer (self := instNumericLimitsUInt8)) == true
  assert! (NumericLimits.is_bounded (self := instNumericLimitsUInt8)) == true
  assert! (NumericLimits.is_modulo (self := instNumericLimitsUInt8)) == true

-- UInt16
#eval do
  assert! (NumericLimits.min : UInt16) == 0
  assert! (NumericLimits.max : UInt16) == 65535
  assert! (NumericLimits.is_signed (self := instNumericLimitsUInt16)) == false

-- UInt32
#eval do
  assert! (NumericLimits.min : UInt32) == 0
  assert! (NumericLimits.max : UInt32) == 4294967295
  assert! (NumericLimits.is_signed (self := instNumericLimitsUInt32)) == false

-- UInt64
#eval do
  assert! (NumericLimits.min : UInt64) == 0
  assert! (NumericLimits.max : UInt64) == 18446744073709551615
  assert! (NumericLimits.is_signed (self := instNumericLimitsUInt64)) == false

-- Int8
#eval do
  assert! (NumericLimits.min : Int8).val == -128
  assert! (NumericLimits.max : Int8).val == 127
  assert! (NumericLimits.is_signed (self := instNumericLimitsInt8)) == true
  assert! (NumericLimits.is_modulo (self := instNumericLimitsInt8)) == false

-- Int16
#eval do
  assert! (NumericLimits.min : Int16).val == -32768
  assert! (NumericLimits.max : Int16).val == 32767
  assert! (NumericLimits.is_signed (self := instNumericLimitsInt16)) == true

-- Int32
#eval do
  assert! (NumericLimits.min : Int32).val == -2147483648
  assert! (NumericLimits.max : Int32).val == 2147483647
  assert! (NumericLimits.is_signed (self := instNumericLimitsInt32)) == true

-- Int64
#eval do
  assert! (NumericLimits.min : Int64).val == -9223372036854775808
  assert! (NumericLimits.max : Int64).val == 9223372036854775807
  assert! (NumericLimits.is_signed (self := instNumericLimitsInt64)) == true

/-! ## cmp_equal tests -/

-- Same-type unsigned comparison
#eval do
  assert! cmp_equal (42 : UInt32) (42 : UInt32) == true
  assert! cmp_equal (42 : UInt32) (43 : UInt32) == false

-- Cross-signedness: negative signed vs unsigned
#eval do
  let neg : Int8 := Int8.mk' (-1)
  assert! cmp_equal neg (0 : UInt8) == false
  -- A negative signed value is never equal to any unsigned value

-- Cross-signedness: positive match
#eval do
  let pos : Int8 := Int8.mk' 42
  assert! cmp_equal pos (42 : UInt8) == true

/-! ## cmp_less tests -/

-- Negative signed is less than any unsigned
#eval do
  let neg : Int8 := Int8.mk' (-1)
  assert! cmp_less neg (0 : UInt8) == true
  assert! cmp_less (0 : UInt8) neg == false

-- Same-type ordering
#eval do
  assert! cmp_less (10 : UInt32) (20 : UInt32) == true
  assert! cmp_less (20 : UInt32) (10 : UInt32) == false
  assert! cmp_less (10 : UInt32) (10 : UInt32) == false

/-! ## cmp_greater tests -/

#eval do
  assert! cmp_greater (20 : UInt32) (10 : UInt32) == true
  assert! cmp_greater (10 : UInt32) (20 : UInt32) == false
  let neg : Int8 := Int8.mk' (-5)
  assert! cmp_greater (0 : UInt8) neg == true
  assert! cmp_greater neg (0 : UInt8) == false

/-! ## in_range tests -/

-- 255 fits in UInt8
#eval do
  assert! in_range UInt8 (255 : UInt16) == true
  -- 256 does not fit in UInt8
  assert! in_range UInt8 (256 : UInt16) == false

-- Negative values don't fit in unsigned types
#eval do
  let neg : Int8 := Int8.mk' (-1)
  assert! in_range UInt8 neg == false

-- Positive Int8 value fits in UInt8
#eval do
  let pos : Int8 := Int8.mk' 100
  assert! in_range UInt8 pos == true

-- UInt8 value 200 does not fit in Int8 (max 127)
#eval do
  assert! in_range Int8 (200 : UInt8) == false

-- UInt8 value 100 fits in Int8
#eval do
  assert! in_range Int8 (100 : UInt8) == true

end Cpp.Numeric.Tests

namespace Cpp

Test negative_never_equals_unsigned :=
  show cmp_equal (Int8.mk' (-1)) (0 : UInt8) = false from rfl

Test negative_less_than_unsigned :=
  show cmp_less (Int8.mk' (-1)) (0 : UInt8) = true from rfl

Test cmp_equal_symmetric :=
  show cmp_equal (42 : UInt32) (42 : UInt32) = cmp_equal (42 : UInt32) (42 : UInt32) from rfl

Test cmp_less_irreflexive :=
  show cmp_less (42 : UInt32) (42 : UInt32) = false from rfl

Test cmp_less_asymmetric :=
  show cmp_less (10 : UInt32) (20 : UInt32) = true from rfl

Test in_range_min :=
  show in_range UInt8 (NumericLimits.min : UInt8) = true from rfl

Test in_range_max :=
  show in_range UInt8 (NumericLimits.max : UInt8) = true from rfl

Test negative_not_in_unsigned_range :=
  show in_range UInt8 (Int8.mk' (-1)) = false from rfl

Test lowest_eq_min_for_integers :=
  show IntPromotable.toInt (NumericLimits.lowest : UInt8) = IntPromotable.toInt (NumericLimits.min : UInt8) from rfl

end Cpp
