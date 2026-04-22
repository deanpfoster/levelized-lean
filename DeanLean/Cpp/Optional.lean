import DeanLean.Cpp.Defs.Optional
import DeanLean.Cpp.Proofs.Optional
import DeanLean.Cpp.Tests.Optional

/-! # C++ std::optional (§22.5)

  Optional object that may or may not contain a value.
  Includes monadic operations (and_then, transform, or_else).
  Corresponds to N4950 §22.5.1–22.5.3.8.
-/

namespace Cpp.Optional

variable {T U V : Type}

Signature Cpp.Optional.has_value : Optional T → Bool
Signature Cpp.Optional.value_or : Optional T → T → T
Signature Cpp.Optional.emplace : Optional T → T → Optional T
Signature Cpp.Optional.reset : Optional T → Optional T
Signature Cpp.Optional.and_then : Optional T → (T → Optional U) → Optional U
Signature Cpp.Optional.transform : Optional T → (T → U) → Optional U
Signature Cpp.Optional.or_else : Optional T → (Unit → Optional T) → Optional T
Signature Cpp.Optional.toOption : Optional T → Option T
Signature Cpp.Optional.ofOption : Option T → Optional T

ProvenTheorem has_value_some : ∀ (v : T), (Optional.some v).has_value = true
ProvenTheorem has_value_nullopt : (Optional.nullopt : Optional T).has_value = false
ProvenTheorem value_some : ∀ [Inhabited T] (v : T), (Optional.some v).value = v
ProvenTheorem value_or_some : ∀ (v d : T), (Optional.some v).value_or d = v
ProvenTheorem value_or_nullopt : ∀ (d : T), (Optional.nullopt).value_or d = d
ProvenTheorem emplace_has_value : ∀ (o : Optional T) (v : T),
    (o.emplace v).has_value = true
ProvenTheorem reset_has_value : ∀ (o : Optional T), o.reset.has_value = false
ProvenTheorem and_then_some : ∀ (v : T) (f : T → Optional U),
    (Optional.some v).and_then f = f v
ProvenTheorem and_then_nullopt : ∀ (f : T → Optional U),
    (Optional.nullopt).and_then f = Optional.nullopt
ProvenTheorem transform_some : ∀ (v : T) (f : T → U),
    (Optional.some v).transform f = Optional.some (f v)
ProvenTheorem transform_nullopt : ∀ (f : T → U),
    (Optional.nullopt : Optional T).transform f = Optional.nullopt
ProvenTheorem or_else_some : ∀ (v : T) (f : Unit → Optional T),
    (Optional.some v).or_else f = Optional.some v
ProvenTheorem or_else_nullopt : ∀ (f : Unit → Optional T),
    (Optional.nullopt).or_else f = f ()
ProvenTheorem roundtrip_to_option : ∀ (o : Optional T),
    Optional.ofOption o.toOption = o
ProvenTheorem roundtrip_of_option : ∀ (o : Option T),
    (Optional.ofOption o).toOption = o
ProvenTheorem monad_pure_and_then : ∀ (v : T) (f : T → Optional U),
    (pure v : Optional T) >>= f = f v
ProvenTheorem monad_nullopt_bind : ∀ (f : T → Optional U),
    (Optional.nullopt : Optional T) >>= f = Optional.nullopt

/-! ## Monadic laws (tested, not yet proven for all cases) -/

TestedConjecture monad_left_identity : ∀ (a : T) (f : T → Optional U),
    (pure a : Optional T) >>= f = f a

TestedConjecture monad_right_identity : ∀ (m : Optional T),
    m >>= (pure · : T → Optional T) = m

TestedConjecture monad_associativity : ∀ (m : Optional T) (f : T → Optional U)
    (g : U → Optional V),
    (m >>= f) >>= g = m >>= (fun x => f x >>= g)

/-! ## transform preserves structure (functor law) -/

TestedConjecture transform_compose : ∀ (o : Optional T) (f : T → U) (g : U → V),
    (o.transform f).transform g = o.transform (g ∘ f)

TestedConjecture transform_id : ∀ (o : Optional T),
    o.transform id = o

/-! ## and_then/or_else interaction -/

TestedConjecture or_else_and_then_nullopt : ∀ (f : Unit → Optional T) (g : T → Optional U),
    ((Optional.nullopt).or_else f).and_then g = (f ()).and_then g

end Cpp.Optional
