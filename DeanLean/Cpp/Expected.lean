import DeanLean.Cpp.Defs.Expected
import DeanLean.Cpp.Proofs.Expected
import DeanLean.Cpp.Tests.Expected

/-! # C++ std::expected (section 22.8)

  Expected object that holds either a value of type T or an error of type E.
  Type parameters are ordered (E, T) to match Lean's Except and enable the Monad instance.
  Includes monadic operations (and_then, transform, transform_error, or_else).
  Corresponds to N4950 section 22.8.1-22.8.6.7.
-/

namespace Cpp.Expected

variable {T U V E E2 : Type}

Signature Cpp.Expected.has_value : Expected E T → Bool
Signature Cpp.Expected.value_or : Expected E T → T → T
Signature Cpp.Expected.and_then : Expected E T → (T → Expected E U) → Expected E U
Signature Cpp.Expected.transform : Expected E T → (T → U) → Expected E U
Signature Cpp.Expected.transform_error : Expected E T → (E → E2) → Expected E2 T
Signature Cpp.Expected.or_else : Expected E T → (E → Expected E2 T) → Expected E2 T
Signature Cpp.Expected.toExcept : Expected E T → Except E T
Signature Cpp.Expected.ofExcept : Except E T → Expected E T

/-! ## Observers -/

ProvenTheorem has_value_ok : ∀ (v : T), (Expected.ok v : Expected E T).has_value = true
ProvenTheorem has_value_unexpected : ∀ (e : E), (Expected.unexpected e : Expected E T).has_value = false
ProvenTheorem value_ok : ∀ [Inhabited T] (v : T), (Expected.ok v : Expected E T).value = v
ProvenTheorem error_unexpected : ∀ [Inhabited E] (e : E), (Expected.unexpected e : Expected E T).error = e
ProvenTheorem value_or_ok : ∀ (v : T) (d : T), (Expected.ok v : Expected E T).value_or d = v
ProvenTheorem value_or_unexpected : ∀ (e : E) (d : T), (Expected.unexpected e : Expected E T).value_or d = d

/-! ## Monadic operations -/

ProvenTheorem and_then_ok : ∀ (v : T) (f : T → Expected E U),
    (Expected.ok v : Expected E T).and_then f = f v
ProvenTheorem and_then_unexpected : ∀ (e : E) (f : T → Expected E U),
    (Expected.unexpected e : Expected E T).and_then f = Expected.unexpected e
ProvenTheorem transform_ok : ∀ (v : T) (f : T → U),
    (Expected.ok v : Expected E T).transform f = Expected.ok (f v)
ProvenTheorem transform_unexpected : ∀ (e : E) (f : T → U),
    (Expected.unexpected e : Expected E T).transform f = Expected.unexpected e
ProvenTheorem transform_error_ok : ∀ (v : T) (f : E → E2),
    (Expected.ok v : Expected E T).transform_error f = Expected.ok v
ProvenTheorem transform_error_unexpected : ∀ (e : E) (f : E → E2),
    (Expected.unexpected e : Expected E T).transform_error f = Expected.unexpected (f e)
ProvenTheorem or_else_ok : ∀ (v : T) (f : E → Expected E2 T),
    (Expected.ok v : Expected E T).or_else f = Expected.ok v
ProvenTheorem or_else_unexpected : ∀ (e : E) (f : E → Expected E2 T),
    (Expected.unexpected e : Expected E T).or_else f = f e

/-! ## Conversions with Except -/

ProvenTheorem roundtrip_to_except : ∀ (x : Expected E T),
    Expected.ofExcept x.toExcept = x
ProvenTheorem roundtrip_of_except : ∀ (x : Except E T),
    (Expected.ofExcept x).toExcept = x

/-! ## Bind with pure/unexpected -/

ProvenTheorem monad_pure_bind : ∀ (v : T) (f : T → Expected E U),
    (pure v : Expected E T) >>= f = f v
ProvenTheorem monad_unexpected_bind : ∀ (e : E) (f : T → Expected E U),
    (Expected.unexpected e : Expected E T) >>= f = Expected.unexpected e

/-! ## Monad laws (tested, not yet proven for all cases) -/

TestedConjecture monad_left_identity : ∀ (a : T) (f : T → Expected E U),
    (pure a : Expected E T) >>= f = f a

TestedConjecture monad_right_identity : ∀ (m : Expected E T),
    m >>= (pure · : T → Expected E T) = m

TestedConjecture monad_associativity : ∀ (m : Expected E T) (f : T → Expected E U)
    (g : U → Expected E V),
    (m >>= f) >>= g = m >>= (fun x => f x >>= g)

/-! ## Functor laws (tested) -/

TestedConjecture transform_compose : ∀ (x : Expected E T) (f : T → U) (g : U → V),
    (x.transform f).transform g = x.transform (g ∘ f)

TestedConjecture transform_id : ∀ (x : Expected E T),
    x.transform id = x

/-! ## or_else/and_then interaction -/

TestedConjecture or_else_and_then_unexpected : ∀ (e : E) (f : E → Expected E2 T) (g : T → Expected E2 U),
    ((Expected.unexpected e : Expected E T).or_else f).and_then g = (f e).and_then g

end Cpp.Expected
