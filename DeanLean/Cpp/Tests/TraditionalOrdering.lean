/-!
# What Ordering.lean would look like in traditional Lean style

This file is NOT part of the build. It's a demonstration of how the same
content would appear without the Lean Manifests conventions — everything
in one file, definitions interleaved with proofs, no manifest/proof
separation.

Compare with our 4-file version:
  - Ordering.lean (header)       — 144 lines, what's true
  - Code/Ordering.lean           — 447 lines, definitions + instances
  - Proofs/Ordering.lean         — 167 lines, derived properties
  - Tests/Ordering.lean          — 191 lines, tests

Total: ~949 lines across 4 files, but a reader only needs 144 lines.

This traditional version: ~300 lines in 1 file, all must be read.
-/

-- ═══════════════════════════════════════════════════════════════
-- In traditional Lean, everything lives in one file.
-- A reader MUST scan the entire file to understand the API.
-- ═══════════════════════════════════════════════════════════════

inductive MyOrdering where
  | lt | eq | gt
deriving Repr, BEq, DecidableEq

namespace MyOrdering

def flip : MyOrdering → MyOrdering
  | .lt => .gt | .eq => .eq | .gt => .lt

theorem flip_flip (o : MyOrdering) : o.flip.flip = o := by cases o <;> rfl

-- Reader must scroll past this to find the next definition...

end MyOrdering

class MyStrongOrd (T : Type) where
  cmp : T → T → MyOrdering
  cmp_refl : ∀ (a : T), cmp a a = .eq
  cmp_flip : ∀ (a b : T), (cmp a b).flip = cmp b a
  cmp_lt_trans : ∀ (a b c : T), cmp a b = .lt → cmp b c = .lt → cmp a c = .lt
  cmp_eq_trans : ∀ (a b c : T), cmp a b = .eq → cmp b c = .eq → cmp a c = .eq

namespace MyStrongOrd
variable {T : Type} [MyStrongOrd T]

-- In traditional style, derived theorems are INTERLEAVED with the
-- class definition. A reader looking for "what does this module provide"
-- must parse every proof to find the next theorem statement.

theorem flip_lt_means_gt (a b : T) (h : cmp a b = .lt) : cmp b a = .gt := by
  have hf := cmp_flip a b; rw [h] at hf; exact hf.symm

-- 15 lines of proof for gt_trans...
theorem cmp_gt_trans (a b c : T)
    (hab : cmp a b = .gt) (hbc : cmp b c = .gt) : cmp a c = .gt := by
  have hba := flip_lt_means_gt b a (by have := cmp_flip a b; rw [hab] at this; exact this.symm)
  have hcb := flip_lt_means_gt c b (by have := cmp_flip b c; rw [hbc] at this; exact this.symm)
  have hca := cmp_lt_trans c b a hcb hba
  exact by have := cmp_flip c a; rw [hca] at this; exact this.symm

-- ...then the reader encounters the Nat instance.
-- But wait — is this part of the API or an implementation detail?
-- In traditional Lean there's no way to tell.

end MyStrongOrd

private def natCmp' (a b : Nat) : MyOrdering :=
  if a < b then .lt else if a = b then .eq else .gt

-- These proofs are NECESSARY to define the instance but IRRELEVANT
-- to any consumer. In traditional Lean, they're right here in your face.

private theorem nat_cmp_refl' (a : Nat) : natCmp' a a = .eq := by
  unfold natCmp'; simp

private theorem nat_cmp_flip' (a b : Nat) : (natCmp' a b).flip = natCmp' b a := by
  unfold natCmp' MyOrdering.flip
  by_cases hab : a < b
  · simp [hab]; have : ¬(b < a) := by omega; have : ¬(b = a) := by omega; simp [*]
  · by_cases heq : a = b
    · subst heq; simp
    · simp [hab, heq]; have : b < a := by omega; simp [*]

private theorem nat_cmp_lt_trans' (a b c : Nat)
    (hab : natCmp' a b = .lt) (hbc : natCmp' b c = .lt) : natCmp' a c = .lt := by
  unfold natCmp' at *
  by_cases h1 : a < b
  · by_cases h2 : b < c
    · have : a < c := by omega; simp [*]
    · simp [h2] at hbc; by_cases h3 : b = c <;> simp [h3] at hbc
  · simp [h1] at hab; by_cases h4 : a = b <;> simp [h4] at hab

private theorem nat_cmp_eq_trans' (a b c : Nat)
    (hab : natCmp' a b = .eq) (hbc : natCmp' b c = .eq) : natCmp' a c = .eq := by
  unfold natCmp' at *
  by_cases h1 : a < b
  · simp [h1] at hab
  · simp [h1] at hab
    by_cases h2 : a = b
    · by_cases h3 : b < c
      · simp [h3] at hbc
      · simp [h3] at hbc; by_cases h4 : b = c
        · subst h2; subst h4; simp
        · simp [h4] at hbc
    · simp [h2] at hab

instance : MyStrongOrd Nat where
  cmp := natCmp'
  cmp_refl := nat_cmp_refl'
  cmp_flip := nat_cmp_flip'
  cmp_lt_trans := nat_cmp_lt_trans'
  cmp_eq_trans := nat_cmp_eq_trans'

-- ═══════════════════════════════════════════════════════════════
-- THE PROBLEM: A reader (human or LLM) wanting to know
-- "what does this module guarantee?" must read ALL of the above.
--
-- In the Lean Manifests layout, they read ONLY the manifest:
--
--   ProvenTheorem strongCmp_refl : ∀ (a : T), strongCmp a a = .eq
--   ProvenTheorem strongCmp_flip : ∀ (a b : T), (strongCmp a b).flip = strongCmp b a
--   ProvenTheorem strongCmp_lt_trans : ...
--   ProvenTheorem strongCmp_gt_trans : ...
--   ProvenTheorem strongCmp_trichotomy : ...
--   ProvenTheorem pair_cmp_eq_iff : ...
--
-- And they can SEE the evidence level:
--   - ProvenTheorem = fully proven
--   - TestedConjecture = tested but not proven (with compiler-enforced witness)
--   - UnprovenConjecture = asserted, zero evidence
--
-- Lean modules give you namespace separation.
-- They do NOT give you:
--   1. Evidence-level metadata (proven vs tested vs unproven)
--   2. Separation of WHAT from WHY (theorem statements from proofs)
--   3. An API surface you can read without parsing proofs
--   4. Recompilation isolation (changing a proof rebuilds nothing above)
--   5. LLM-friendly context (144 lines vs 447+167+191)
-- ═══════════════════════════════════════════════════════════════
