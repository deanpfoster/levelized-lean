import DeanLean.Cpp.Defs.Concepts
import DeanLean.Cpp.Proofs.Concepts
import DeanLean.Cpp.Tests.Concepts

/-! # C++ Concepts Library (§18)

  Formalizes the C++ <concepts> header from N4950 §18.
  Concepts are modeled as Lean typeclasses with laws.

  §18.4  Language-related concepts: same_as, derived_from, convertible_to,
         integral, signed_integral, unsigned_integral, floating_point
  §18.5  Comparison concepts: equality_comparable, totally_ordered
  §18.6  Object concepts: semiregular, regular
  §18.7  Callable concepts: invocable, regular_invocable, predicate, relation
-/

namespace Cpp.Concepts

variable {T U : Type}
variable {F : Type}

-- ============================================================================
-- §18.4.2 same_as
-- ============================================================================

Signature Cpp.same_as_symm : same_as T U → same_as U T

-- ============================================================================
-- §18.4.7 Arithmetic concept relationships
-- ============================================================================

Signature Cpp.signed_integral_is_integral : (T : Type) → [SignedIntegral T] → Integral T
Signature Cpp.unsigned_integral_is_integral : (T : Type) → [UnsignedIntegral T] → Integral T

-- ============================================================================
-- §18.6 Object concept relationships
-- ============================================================================

Signature Cpp.regular_is_semiregular : (T : Type) → [Regular T] → Semiregular T
Signature Cpp.totally_ordered_is_equality_comparable :
    (T : Type) → [TotallyOrdered T] → EqualityComparable T

-- ============================================================================
-- Proven Prop-valued relationships (§18.4.2)
-- ============================================================================

ProvenTheorem same_as_symmetric :
    same_as T U → same_as U T
ProvenTheorem same_as_refl :
    same_as T T

-- ============================================================================
-- Data-valued relationships: use Wrap since they produce typeclass instances
-- (not Props), which cannot be theorems in Lean.
-- ============================================================================

-- §18.4.7
Wrap signed_integral_implies_integral :=
    @Cpp.Concepts.signed_integral_implies_integral_proof
Wrap unsigned_integral_implies_integral :=
    @Cpp.Concepts.unsigned_integral_implies_integral_proof

-- §18.6
Wrap regular_implies_semiregular :=
    @Cpp.Concepts.regular_implies_semiregular_proof
Wrap regular_implies_equality_comparable :=
    @Cpp.Concepts.regular_implies_equality_comparable_proof
Wrap regular_implies_copy_constructible :=
    @Cpp.Concepts.regular_implies_copy_constructible_proof
Wrap semiregular_implies_copy_constructible :=
    @Cpp.Concepts.semiregular_implies_copy_constructible_proof
Wrap semiregular_implies_default_initializable :=
    @Cpp.Concepts.semiregular_implies_default_initializable_proof

-- §18.4.14 / §18.4.13
Wrap copy_constructible_implies_move_constructible :=
    @Cpp.Concepts.copy_constructible_implies_move_constructible_proof

-- §18.5.5
Wrap totally_ordered_implies_equality_comparable :=
    @Cpp.Concepts.totally_ordered_implies_equality_comparable_proof

-- §18.4.3
Wrap derived_from_implies_convertible_to :=
    @Cpp.Concepts.derived_from_implies_convertible_to_proof

-- §18.7
Wrap regular_invocable_implies_invocable :=
    @Cpp.Concepts.regular_invocable_implies_invocable_proof

-- Built-in type instances
Wrap nat_is_unsigned_integral :=
    @Cpp.Concepts.nat_is_unsigned_integral_proof
Wrap nat_is_integral :=
    @Cpp.Concepts.nat_is_integral_proof
Wrap int_is_signed_integral :=
    @Cpp.Concepts.int_is_signed_integral_proof
Wrap int_is_integral :=
    @Cpp.Concepts.int_is_integral_proof
Wrap float_is_floating_point :=
    @Cpp.Concepts.float_is_floating_point_proof
Wrap nat_convertible_to_int :=
    @Cpp.Concepts.nat_convertible_to_int_proof

end Cpp.Concepts
