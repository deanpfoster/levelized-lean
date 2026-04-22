import DeanLean.Cpp.Defs.Pair
import DeanLean.Cpp.Proofs.Pair
import DeanLean.Cpp.Tests.Pair

/-! # C++ std::pair (§22.3)

  Heterogeneous pair of values with lexicographic comparison.
  Corresponds to N4950 §22.3.1–22.3.5.
-/

namespace Cpp.Pair

variable {T1 T2 U1 U2 : Type}

Signature Cpp.Pair.make : T1 → T2 → Pair T1 T2
Signature Cpp.Pair.swap : Pair T1 T2 → Pair T2 T1
Signature Cpp.Pair.map_first : (T1 → U1) → Pair T1 T2 → Pair U1 T2
Signature Cpp.Pair.map_second : (T2 → U2) → Pair T1 T2 → Pair T1 U2
Signature Cpp.Pair.tuple_size : Pair T1 T2 → Nat

Wrap tuple_size_is_2_proof := @Cpp.Pair.tuple_size_proof

ProvenTheorem swap_swap : ∀ (p : Pair T1 T2), p.swap.swap = p
ProvenTheorem swap_first : ∀ (p : Pair T1 T2), p.swap.first = p.second
ProvenTheorem swap_second : ∀ (p : Pair T1 T2), p.swap.second = p.first
ProvenTheorem make_first : ∀ (a : T1) (b : T2), (Pair.make a b).first = a
ProvenTheorem make_second : ∀ (a : T1) (b : T2), (Pair.make a b).second = b
ProvenTheorem eq_iff_components : ∀ (p q : Pair T1 T2),
    p = q ↔ p.first = q.first ∧ p.second = q.second
ProvenTheorem map_first_id : ∀ (p : Pair T1 T2), p.map_first id = p
ProvenTheorem map_second_id : ∀ (p : Pair T1 T2), p.map_second id = p
ProvenTheorem tuple_size_is_2 : ∀ (p : Pair T1 T2), p.tuple_size = 2

end Cpp.Pair
