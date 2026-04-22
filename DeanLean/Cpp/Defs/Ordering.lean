import DeanLean.Basic
import DeanLean.Cpp.Code.Pair

/-! # C++ comparison/ordering types (N4950 §17.11)

  Formalizes the three comparison category types:
  - `strong_ordering` (§17.11.2.4): total order with substitutability
  - `weak_ordering` (§17.11.2.3): total order without substitutability
  - `partial_ordering` (§17.11.2.2): partial order, allows unordered

  Also provides the `StrongOrd` typeclass with laws, instances for
  Nat and Int, and a lexicographic lifting for Pair.
-/

namespace Cpp

/-! ## Comparison category types -/

/-- C++ `strong_ordering` (§17.11.2.4).
    Result type for three-way comparison where equality implies substitutability.
    Valid values: less, equal, equivalent (same as equal), greater. -/
inductive Ordering where
  | lt
  | eq
  | gt
deriving Repr, BEq, DecidableEq, Inhabited

/-- C++ `weak_ordering` (§17.11.2.3).
    Result type for three-way comparison where equality does not
    imply substitutability. -/
inductive WeakOrdering where
  | lt
  | equivalent
  | gt
deriving Repr, BEq, DecidableEq, Inhabited

/-- C++ `partial_ordering` (§17.11.2.2).
    Result type for three-way comparison that permits incomparable values. -/
inductive PartialOrdering where
  | lt
  | equivalent
  | gt
  | unordered
deriving Repr, BEq, DecidableEq, Inhabited

namespace Ordering

/-- Convert strong_ordering to weak_ordering (§17.11.2.4 conversions) -/
def toWeak : Ordering → WeakOrdering
  | .lt => .lt
  | .eq => .equivalent
  | .gt => .gt

/-- Convert strong_ordering to partial_ordering (§17.11.2.4 conversions) -/
def toPartial : Ordering → PartialOrdering
  | .lt => .lt
  | .eq => .equivalent
  | .gt => .gt

/-- Flip the ordering (reverse comparison direction) -/
def flip : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-- flip is an involution -/
theorem flip_flip (o : Ordering) : o.flip.flip = o := by
  cases o <;> rfl

/-- Named comparison functions from §17.11.1 -/
def is_eq (o : Ordering) : Bool := o == .eq
def is_neq (o : Ordering) : Bool := o != .eq
def is_lt (o : Ordering) : Bool := o == .lt
def is_lteq (o : Ordering) : Bool := o == .lt || o == .eq
def is_gt (o : Ordering) : Bool := o == .gt
def is_gteq (o : Ordering) : Bool := o == .gt || o == .eq

end Ordering

namespace WeakOrdering

/-- Convert weak_ordering to partial_ordering (§17.11.2.3 conversions) -/
def toPartial : WeakOrdering → PartialOrdering
  | .lt => .lt
  | .equivalent => .equivalent
  | .gt => .gt

end WeakOrdering

namespace PartialOrdering

/-- Named comparison functions from §17.11.1 -/
def is_eq (o : PartialOrdering) : Bool := o == .equivalent
def is_neq (o : PartialOrdering) : Bool := o != .equivalent
def is_lt (o : PartialOrdering) : Bool := o == .lt
def is_lteq (o : PartialOrdering) : Bool := o == .lt || o == .equivalent
def is_gt (o : PartialOrdering) : Bool := o == .gt
def is_gteq (o : PartialOrdering) : Bool := o == .gt || o == .equivalent

end PartialOrdering

/-! ## StrongOrd typeclass

  A typeclass for types with a three-way comparison function that
  satisfies the laws of a strong (total) ordering per §17.11.2.4:
  - Reflexivity: cmp a a = eq
  - Flip/Antisymmetry: (cmp a b).flip = cmp b a
  - Lt-transitivity: cmp a b = lt and cmp b c = lt implies cmp a c = lt
  - Eq-transitivity: cmp a b = eq and cmp b c = eq implies cmp a c = eq
    (This captures substitutability: equal elements are interchangeable.)
-/

class StrongOrd (T : Type) where
  strongCmp : T → T → Ordering
  /-- Reflexivity: comparing any element with itself yields eq -/
  cmp_refl : ∀ (a : T), strongCmp a a = .eq
  /-- Antisymmetry via flip: flipping the result reverses the arguments -/
  cmp_flip : ∀ (a b : T), (strongCmp a b).flip = strongCmp b a
  /-- Transitivity of lt -/
  cmp_lt_trans : ∀ (a b c : T),
    strongCmp a b = .lt → strongCmp b c = .lt → strongCmp a c = .lt
  /-- Transitivity of eq (substitutability) -/
  cmp_eq_trans : ∀ (a b c : T),
    strongCmp a b = .eq → strongCmp b c = .eq → strongCmp a c = .eq

namespace StrongOrd

variable {T : Type} [StrongOrd T]

/-- If cmp a b = lt then cmp b a = gt -/
theorem flip_lt_means_gt (a b : T) (h : strongCmp a b = .lt) :
    strongCmp b a = .gt := by
  have hf := cmp_flip a b; rw [h] at hf; exact hf.symm

/-- If cmp a b = gt then cmp b a = lt -/
theorem flip_gt_means_lt (a b : T) (h : strongCmp a b = .gt) :
    strongCmp b a = .lt := by
  have hf := cmp_flip a b; rw [h] at hf; exact hf.symm

/-- If cmp a b = eq then cmp b a = eq -/
theorem flip_eq_means_eq (a b : T) (h : strongCmp a b = .eq) :
    strongCmp b a = .eq := by
  have hf := cmp_flip a b; rw [h] at hf; exact hf.symm

/-- Transitivity of gt -/
theorem cmp_gt_trans (a b c : T)
    (hab : strongCmp a b = .gt) (hbc : strongCmp b c = .gt) :
    strongCmp a c = .gt := by
  have hba := flip_gt_means_lt a b hab
  have hcb := flip_gt_means_lt b c hbc
  have hca := cmp_lt_trans c b a hcb hba
  exact flip_lt_means_gt c a hca

/-- Symmetry: cmp a b = .lt iff cmp b a = .gt -/
theorem cmp_lt_iff_gt (a b : T) :
    strongCmp a b = .lt ↔ strongCmp b a = .gt :=
  ⟨flip_lt_means_gt a b, flip_gt_means_lt b a⟩

/-- Trichotomy: the result is one of lt/eq/gt -/
theorem cmp_trichotomy (a b : T) :
    strongCmp a b = .lt ∨ strongCmp a b = .eq ∨ strongCmp a b = .gt := by
  cases h : strongCmp a b
  · left; rfl
  · right; left; rfl
  · right; right; rfl

/-- Eq is symmetric -/
theorem cmp_eq_symm (a b : T) (h : strongCmp a b = .eq) :
    strongCmp b a = .eq :=
  flip_eq_means_eq a b h

/-- If cmp a b = lt and cmp b c = eq then cmp a c = lt -/
theorem cmp_lt_eq_trans (a b c : T)
    (hab : strongCmp a b = .lt) (hbc : strongCmp b c = .eq) :
    strongCmp a c = .lt := by
  cases hac : strongCmp a c with
  | lt => rfl
  | eq =>
    have hcb := flip_eq_means_eq b c hbc
    have hab_eq := cmp_eq_trans a c b hac hcb
    rw [hab] at hab_eq; exact absurd hab_eq (by decide)
  | gt =>
    have hca := flip_gt_means_lt a c hac
    have hcb := cmp_lt_trans c a b hca hab
    have hcb_eq := flip_eq_means_eq b c hbc
    rw [hcb_eq] at hcb; exact absurd hcb (by decide)

/-- If cmp a b = eq and cmp b c = lt then cmp a c = lt -/
theorem cmp_eq_lt_trans (a b c : T)
    (hab : strongCmp a b = .eq) (hbc : strongCmp b c = .lt) :
    strongCmp a c = .lt := by
  cases hac : strongCmp a c with
  | lt => rfl
  | eq =>
    have hca := flip_eq_means_eq a c hac
    have hcb_eq := cmp_eq_trans c a b hca hab
    have hcb_gt := flip_lt_means_gt b c hbc
    rw [hcb_gt] at hcb_eq; exact absurd hcb_eq (by decide)
  | gt =>
    have hca := flip_gt_means_lt a c hac
    have hba := flip_eq_means_eq a b hab
    have hcb := cmp_lt_eq_trans c a b hca hab
    have hbc_gt := flip_lt_means_gt b c hbc
    rw [hbc_gt] at hcb; exact absurd hcb (by decide)

/-- Gt composed with eq on the right -/
theorem cmp_gt_eq_trans (a b c : T)
    (hab : strongCmp a b = .gt) (hbc : strongCmp b c = .eq) :
    strongCmp a c = .gt := by
  have hba := flip_gt_means_lt a b hab
  have hcb := flip_eq_means_eq b c hbc
  have hca := cmp_eq_lt_trans c b a hcb hba
  exact flip_lt_means_gt c a hca

/-- Eq composed with gt -/
theorem cmp_eq_gt_trans (a b c : T)
    (hab : strongCmp a b = .eq) (hbc : strongCmp b c = .gt) :
    strongCmp a c = .gt := by
  have hcb := flip_gt_means_lt b c hbc
  have hba := flip_eq_means_eq a b hab
  have hca := cmp_lt_eq_trans c b a hcb hba
  exact flip_lt_means_gt c a hca

end StrongOrd

/-! ## Instances -/

/-- Three-way comparison of natural numbers -/
def natCmp (a b : Nat) : Ordering :=
  if a < b then .lt
  else if a = b then .eq
  else .gt

/-- Three-way comparison of integers -/
def intCmp (a b : Int) : Ordering :=
  if a < b then .lt
  else if a = b then .eq
  else .gt

private theorem nat_cmp_refl (a : Nat) : natCmp a a = .eq := by
  unfold natCmp; simp

private theorem nat_cmp_flip (a b : Nat) : (natCmp a b).flip = natCmp b a := by
  unfold natCmp Ordering.flip
  by_cases hab : a < b
  · simp [hab]
    have : ¬(b < a) := by omega
    have : ¬(b = a) := by omega
    simp [*]
  · by_cases heq : a = b
    · subst heq; simp
    · simp [hab, heq]
      have : b < a := by omega
      simp [*]

private theorem nat_cmp_lt_trans (a b c : Nat)
    (hab : natCmp a b = .lt) (hbc : natCmp b c = .lt) :
    natCmp a c = .lt := by
  unfold natCmp at *
  by_cases h1 : a < b
  · by_cases h2 : b < c
    · have : a < c := by omega
      simp [*]
    · simp [h2] at hbc
      by_cases h3 : b = c
      · simp [h3] at hbc
      · simp [h3] at hbc
  · simp [h1] at hab
    by_cases h4 : a = b
    · simp [h4] at hab
    · simp [h4] at hab

private theorem nat_cmp_eq_trans (a b c : Nat)
    (hab : natCmp a b = .eq) (hbc : natCmp b c = .eq) :
    natCmp a c = .eq := by
  unfold natCmp at *
  by_cases h1 : a < b
  · simp [h1] at hab
  · simp [h1] at hab
    by_cases h2 : a = b
    · by_cases h3 : b < c
      · simp [h3] at hbc
      · simp [h3] at hbc
        by_cases h4 : b = c
        · subst h2; subst h4; simp
        · simp [h4] at hbc
    · simp [h2] at hab

/-- StrongOrd instance for Nat -/
instance : StrongOrd Nat where
  strongCmp := natCmp
  cmp_refl := nat_cmp_refl
  cmp_flip := nat_cmp_flip
  cmp_lt_trans := nat_cmp_lt_trans
  cmp_eq_trans := nat_cmp_eq_trans

private theorem int_cmp_refl (a : Int) : intCmp a a = .eq := by
  unfold intCmp; simp

private theorem int_cmp_flip (a b : Int) : (intCmp a b).flip = intCmp b a := by
  unfold intCmp Ordering.flip
  by_cases hab : a < b
  · simp [hab]
    have : ¬(b < a) := by omega
    have : ¬(b = a) := by omega
    simp [*]
  · by_cases heq : a = b
    · subst heq; simp
    · simp [hab, heq]
      have : b < a := by omega
      simp [*]

private theorem int_cmp_lt_trans (a b c : Int)
    (hab : intCmp a b = .lt) (hbc : intCmp b c = .lt) :
    intCmp a c = .lt := by
  unfold intCmp at *
  by_cases h1 : a < b
  · by_cases h2 : b < c
    · have : a < c := by omega
      simp [*]
    · simp [h2] at hbc
      by_cases h3 : b = c
      · simp [h3] at hbc
      · simp [h3] at hbc
  · simp [h1] at hab
    by_cases h4 : a = b
    · simp [h4] at hab
    · simp [h4] at hab

private theorem int_cmp_eq_trans (a b c : Int)
    (hab : intCmp a b = .eq) (hbc : intCmp b c = .eq) :
    intCmp a c = .eq := by
  unfold intCmp at *
  by_cases h1 : a < b
  · simp [h1] at hab
  · simp [h1] at hab
    by_cases h2 : a = b
    · by_cases h3 : b < c
      · simp [h3] at hbc
      · simp [h3] at hbc
        by_cases h4 : b = c
        · subst h2; subst h4; simp
        · simp [h4] at hbc
    · simp [h2] at hab

/-- StrongOrd instance for Int -/
instance : StrongOrd Int where
  strongCmp := intCmp
  cmp_refl := int_cmp_refl
  cmp_flip := int_cmp_flip
  cmp_lt_trans := int_cmp_lt_trans
  cmp_eq_trans := int_cmp_eq_trans

/-! ## Lexicographic lifting for Pair -/

/-- Lexicographic comparison for pairs: compare first components, break ties with second.
    This mirrors the C++ operator<=> for std::pair (§22.3.7). -/
def pairCmp {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2]
    (p q : Pair T1 T2) : Ordering :=
  match StrongOrd.strongCmp p.first q.first with
  | .eq => StrongOrd.strongCmp p.second q.second
  | ord => ord

private theorem pair_cmp_refl {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2]
    (p : Pair T1 T2) : pairCmp p p = .eq := by
  unfold pairCmp
  rw [StrongOrd.cmp_refl p.first, StrongOrd.cmp_refl p.second]

private theorem pair_cmp_flip {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2]
    (p q : Pair T1 T2) : (pairCmp p q).flip = pairCmp q p := by
  unfold pairCmp
  cases hf : StrongOrd.strongCmp p.first q.first with
  | lt =>
    have hqf := StrongOrd.flip_lt_means_gt p.first q.first hf
    simp [hqf, Ordering.flip]
  | eq =>
    have hqf := StrongOrd.flip_eq_means_eq p.first q.first hf
    simp [hqf]
    exact StrongOrd.cmp_flip p.second q.second
  | gt =>
    have hqf := StrongOrd.flip_gt_means_lt p.first q.first hf
    simp [hqf, Ordering.flip]

private theorem pair_cmp_lt_trans {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2]
    (p q r : Pair T1 T2)
    (hpq : pairCmp p q = .lt) (hqr : pairCmp q r = .lt) :
    pairCmp p r = .lt := by
  unfold pairCmp at *
  cases hf1 : StrongOrd.strongCmp p.first q.first with
  | lt =>
    simp [hf1] at hpq
    cases hf2 : StrongOrd.strongCmp q.first r.first with
    | lt =>
      simp [hf2] at hqr
      rw [StrongOrd.cmp_lt_trans p.first q.first r.first hf1 hf2]
    | eq =>
      simp [hf2] at hqr
      rw [StrongOrd.cmp_lt_eq_trans p.first q.first r.first hf1 hf2]
    | gt =>
      simp [hf2] at hqr
  | eq =>
    simp [hf1] at hpq
    cases hf2 : StrongOrd.strongCmp q.first r.first with
    | lt =>
      simp [hf2] at hqr
      rw [StrongOrd.cmp_eq_lt_trans p.first q.first r.first hf1 hf2]
    | eq =>
      simp [hf2] at hqr
      rw [StrongOrd.cmp_eq_trans p.first q.first r.first hf1 hf2]
      exact StrongOrd.cmp_lt_trans p.second q.second r.second hpq hqr
    | gt =>
      simp [hf2] at hqr
  | gt =>
    simp [hf1] at hpq

private theorem pair_cmp_eq_trans {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2]
    (p q r : Pair T1 T2)
    (hpq : pairCmp p q = .eq) (hqr : pairCmp q r = .eq) :
    pairCmp p r = .eq := by
  unfold pairCmp at *
  cases hf1 : StrongOrd.strongCmp p.first q.first with
  | lt =>
    simp [hf1] at hpq
  | eq =>
    simp [hf1] at hpq
    cases hf2 : StrongOrd.strongCmp q.first r.first with
    | lt =>
      simp [hf2] at hqr
    | eq =>
      simp [hf2] at hqr
      rw [StrongOrd.cmp_eq_trans p.first q.first r.first hf1 hf2]
      exact StrongOrd.cmp_eq_trans p.second q.second r.second hpq hqr
    | gt =>
      simp [hf2] at hqr
  | gt =>
    simp [hf1] at hpq

/-- Lexicographic StrongOrd for Pair: compare first components, break ties with second.
    This mirrors the C++ operator<=> for std::pair (§22.3.7). -/
instance {T1 T2 : Type} [StrongOrd T1] [StrongOrd T2] : StrongOrd (Pair T1 T2) where
  strongCmp := pairCmp
  cmp_refl := pair_cmp_refl
  cmp_flip := pair_cmp_flip
  cmp_lt_trans := pair_cmp_lt_trans
  cmp_eq_trans := pair_cmp_eq_trans

end Cpp
