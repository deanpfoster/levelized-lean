import DeanLean.Cpp.Code.Numeric
import DeanLean.Cpp.Proofs.Numeric
import DeanLean.Cpp.Tests.Numeric

/-! # C++ numeric_limits (N4950 §17.3.5) and integer comparison (§22.2.7)

  Formalizes `numeric_limits` as a typeclass with instances for
  UInt8, UInt16, UInt32, UInt64, Int8, Int16, Int32, Int64.
  Also formalizes safe integer comparison functions: cmp_equal,
  cmp_less, cmp_greater, and in_range.
-/

namespace Cpp

variable {T U : Type}

/-! ## Signatures for integer comparison functions -/

Signature Cpp.cmp_equal : {T U : Type} → [IntPromotable T] → [IntPromotable U] → T → U → Bool
Signature Cpp.cmp_less : {T U : Type} → [IntPromotable T] → [IntPromotable U] → T → U → Bool
Signature Cpp.cmp_greater : {T U : Type} → [IntPromotable T] → [IntPromotable U] → T → U → Bool
Signature Cpp.in_range : (R : Type) → {T : Type} → [NumericLimits R] → [IntPromotable R] →
    [IntPromotable T] → T → Bool

/-! ## Proven properties: min ≤ max -/

ProvenTheorem NumericLimits.min_le_max_UInt8 : NumericLimits.min_le_max_prop UInt8
ProvenTheorem NumericLimits.min_le_max_UInt16 : NumericLimits.min_le_max_prop UInt16
ProvenTheorem NumericLimits.min_le_max_UInt32 : NumericLimits.min_le_max_prop UInt32
ProvenTheorem NumericLimits.min_le_max_UInt64 : NumericLimits.min_le_max_prop UInt64
ProvenTheorem NumericLimits.min_le_max_Int8 : NumericLimits.min_le_max_prop Int8
ProvenTheorem NumericLimits.min_le_max_Int16 : NumericLimits.min_le_max_prop Int16
ProvenTheorem NumericLimits.min_le_max_Int32 : NumericLimits.min_le_max_prop Int32
ProvenTheorem NumericLimits.min_le_max_Int64 : NumericLimits.min_le_max_prop Int64

/-! ## Proven properties: digits > 0 -/

ProvenTheorem NumericLimits.digits_pos_UInt8 : NumericLimits.digits_pos_prop UInt8
ProvenTheorem NumericLimits.digits_pos_UInt16 : NumericLimits.digits_pos_prop UInt16
ProvenTheorem NumericLimits.digits_pos_UInt32 : NumericLimits.digits_pos_prop UInt32
ProvenTheorem NumericLimits.digits_pos_UInt64 : NumericLimits.digits_pos_prop UInt64
ProvenTheorem NumericLimits.digits_pos_Int8 : NumericLimits.digits_pos_prop Int8
ProvenTheorem NumericLimits.digits_pos_Int16 : NumericLimits.digits_pos_prop Int16
ProvenTheorem NumericLimits.digits_pos_Int32 : NumericLimits.digits_pos_prop Int32
ProvenTheorem NumericLimits.digits_pos_Int64 : NumericLimits.digits_pos_prop Int64

/-! ## Proven properties: is_signed correctness -/

ProvenTheorem NumericLimits.is_signed_correct_Int8 :
    NumericLimits.is_signed_correct_prop Int8
ProvenTheorem NumericLimits.is_signed_correct_Int16 :
    NumericLimits.is_signed_correct_prop Int16
ProvenTheorem NumericLimits.is_signed_correct_Int32 :
    NumericLimits.is_signed_correct_prop Int32
ProvenTheorem NumericLimits.is_signed_correct_Int64 :
    NumericLimits.is_signed_correct_prop Int64

ProvenTheorem NumericLimits.unsigned_min_nonneg_UInt8 :
    NumericLimits.unsigned_min_nonneg_prop UInt8
ProvenTheorem NumericLimits.unsigned_min_nonneg_UInt16 :
    NumericLimits.unsigned_min_nonneg_prop UInt16
ProvenTheorem NumericLimits.unsigned_min_nonneg_UInt32 :
    NumericLimits.unsigned_min_nonneg_prop UInt32
ProvenTheorem NumericLimits.unsigned_min_nonneg_UInt64 :
    NumericLimits.unsigned_min_nonneg_prop UInt64

/-! ## Proven properties: cmp correctness -/

ProvenTheorem cmp_equal_correct :
    ∀ [IntPromotable T] [IntPromotable U] (t : T) (u : U), cmp_equal_correct_prop t u
ProvenTheorem cmp_less_correct :
    ∀ [IntPromotable T] [IntPromotable U] (t : T) (u : U), cmp_less_correct_prop t u
ProvenTheorem cmp_greater_flip :
    ∀ [IntPromotable T] [IntPromotable U] (t : T) (u : U), cmp_greater_flip_prop t u

/-! ## Cross-signedness comparison properties (tested) -/

TestedConjecture negative_never_equals_unsigned :
    ∀ (s : Int8) (u : UInt8), s.val < 0 → cmp_equal s u = false

TestedConjecture negative_less_than_unsigned :
    ∀ (s : Int8) (u : UInt8), s.val < 0 → cmp_less s u = true

TestedConjecture cmp_equal_symmetric :
    ∀ [IntPromotable T] [IntPromotable U] (t : T) (u : U),
    cmp_equal t u = cmp_equal u t

TestedConjecture cmp_less_irreflexive :
    ∀ [IntPromotable T] (t : T), cmp_less t t = false

TestedConjecture cmp_less_asymmetric :
    ∀ [IntPromotable T] [IntPromotable U] (t : T) (u : U),
    cmp_less t u = true → cmp_less u t = false

/-! ## in_range properties (tested) -/

TestedConjecture in_range_min : ∀ (R : Type) [NumericLimits R] [IntPromotable R],
    in_range R (NumericLimits.min : R) = true

TestedConjecture in_range_max : ∀ (R : Type) [NumericLimits R] [IntPromotable R],
    in_range R (NumericLimits.max : R) = true

TestedConjecture negative_not_in_unsigned_range :
    ∀ (s : Int8), s.val < 0 → in_range UInt8 s = false

/-! ## lowest = min for integer types (tested) -/

TestedConjecture lowest_eq_min_for_integers :
    ∀ (T : Type) [NumericLimits T] [IntPromotable T],
    NumericLimits.is_integer (self := ‹NumericLimits T›) = true →
    IntPromotable.toInt (NumericLimits.lowest : T) = IntPromotable.toInt (NumericLimits.min : T)

end Cpp
