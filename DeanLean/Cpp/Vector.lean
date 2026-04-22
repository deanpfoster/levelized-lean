import DeanLean.Cpp.Defs.Vector
import DeanLean.Cpp.Proofs.Vector
import DeanLean.Cpp.Tests.Vector

/-! # C++ std::vector (§24.3.11)

  Dynamic array with amortized O(1) push_back.
  Modeled as a wrapper around `Array T`.
  Corresponds to N4950 §24.3.11.
-/

namespace Cpp.Vector

variable {T : Type}

Signature Cpp.Vector.empty : Vector T
Signature Cpp.Vector.size : Vector T → Nat
Signature Cpp.Vector.isEmpty : Vector T → Bool
Signature Cpp.Vector.clear : Vector T → Vector T
Signature Cpp.Vector.push_back : Vector T → T → Vector T
Signature Cpp.Vector.pop_back : Vector T → Vector T
Signature Cpp.Vector.get : (v : Vector T) → Fin v.size → T
Signature Cpp.Vector.ofList : List T → Vector T
Signature Cpp.Vector.ofArray : Array T → Vector T
Signature Cpp.Vector.toList : Vector T → List T
Signature Cpp.Vector.toArray : Vector T → Array T

ProvenTheorem size_empty : (Vector.empty : Vector T).size = 0
ProvenTheorem size_push_back : ∀ (v : Vector T) (x : T), (v.push_back x).size = v.size + 1
ProvenTheorem size_pop_back : ∀ (v : Vector T), v.size > 0 → (v.pop_back).size = v.size - 1
ProvenTheorem get_push_back_last : ∀ (v : Vector T) (x : T),
    (v.push_back x).get ⟨v.size, by simp [push_back, size, Array.size_push]⟩ = x
ProvenTheorem size_clear : ∀ (v : Vector T), (v.clear).size = 0
ProvenTheorem isEmpty_iff_size_zero : ∀ (v : Vector T), v.isEmpty = true ↔ v.size = 0
ProvenTheorem push_back_pop_back : ∀ (v : Vector T) (h : v.size > 0),
    (v.pop_back).push_back (v.back h) = v

end Cpp.Vector
