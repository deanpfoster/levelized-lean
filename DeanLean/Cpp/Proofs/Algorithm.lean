import DeanLean.Cpp.Code.Algorithm

namespace Cpp

/-! # Proofs for C++ algorithm formalizations (N4950 §27.7-27.9)

  Proven properties of min, max, clamp, isSorted, minElement, maxElement.
  These use `StrongOrd.strongCmp` and the `StrongOrd` / `StrongOrdEq` typeclasses
  where symmetry, transitivity, or equality reflection is needed.
-/

variable {T : Type} [StrongOrd T]

/-! ## Reflexivity and transitivity of cmpLe -/

theorem cmpLe_refl_proof (a : T) : cmpLe a a := by
  unfold cmpLe; rw [StrongOrd.cmp_refl]; decide

theorem cmpLe_trans_proof (a b c : T) :
    cmpLe a b → cmpLe b c → cmpLe a c := by
  unfold cmpLe
  intro hab hbc
  intro hac
  -- strongCmp a c = .gt, so strongCmp c a = .lt
  have hca := StrongOrd.flip_gt_means_lt a c hac
  -- Case split on strongCmp a b
  cases hab' : StrongOrd.strongCmp a b with
  | lt =>
    cases hbc' : StrongOrd.strongCmp b c with
    | lt =>
      have := StrongOrd.cmp_lt_trans a b c hab' hbc'
      rw [this] at hac; exact absurd hac (by decide)
    | eq =>
      have := StrongOrd.cmp_lt_eq_trans a b c hab' hbc'
      rw [this] at hac; exact absurd hac (by decide)
    | gt => exact hbc hbc'
  | eq =>
    cases hbc' : StrongOrd.strongCmp b c with
    | lt =>
      have := StrongOrd.cmp_eq_lt_trans a b c hab' hbc'
      rw [this] at hac; exact absurd hac (by decide)
    | eq =>
      have := StrongOrd.cmp_eq_trans a b c hab' hbc'
      rw [this] at hac; exact absurd hac (by decide)
    | gt => exact hbc hbc'
  | gt => exact hab hab'

/-! ## cppMin properties -/

/-- `cppMin a b` is either `a` or `b`. -/
theorem cppMin_cases_proof (a b : T) : cppMin a b = a ∨ cppMin a b = b := by
  unfold cppMin
  cases StrongOrd.strongCmp a b with
  | lt => left; rfl
  | eq => left; rfl
  | gt => right; rfl

/-- `cppMin a b ≤ a` (in the `cmpLe` sense). -/
theorem cppMin_le_left_proof (a b : T) :
    cmpLe (cppMin a b) a := by
  unfold cppMin cmpLe
  cases hab : StrongOrd.strongCmp a b with
  | lt => rw [StrongOrd.cmp_refl]; decide
  | eq => rw [StrongOrd.cmp_refl]; decide
  | gt => rw [StrongOrd.flip_gt_means_lt a b hab]; decide

/-- `cppMin a b ≤ b` (in the `cmpLe` sense). -/
theorem cppMin_le_right_proof (a b : T) :
    cmpLe (cppMin a b) b := by
  unfold cppMin cmpLe
  cases hab : StrongOrd.strongCmp a b with
  | lt => rw [hab]; decide
  | eq => rw [hab]; decide
  | gt => rw [StrongOrd.cmp_refl]; decide

/-- `cppMin a a = a` for any `a`, given a StrongOrd. -/
theorem cppMin_self_proof (a : T) : cppMin a a = a := by
  unfold cppMin; rw [StrongOrd.cmp_refl]

/-- `cppMin` is commutative when the ordering is lawful and equality-reflecting. -/
theorem cppMin_comm_proof [StrongOrdEq T] (a b : T) :
    cppMin a b = cppMin b a := by
  unfold cppMin
  cases hab : StrongOrd.strongCmp a b with
  | lt => rw [StrongOrd.flip_lt_means_gt a b hab]
  | eq =>
    have heq := StrongOrdEq.cmp_eq_imp_eq a b hab
    subst heq; rw [StrongOrd.cmp_refl]
  | gt => rw [StrongOrd.flip_gt_means_lt a b hab]

/-! ## cppMax properties -/

/-- `cppMax a b` is either `a` or `b`. -/
theorem cppMax_cases_proof (a b : T) : cppMax a b = a ∨ cppMax a b = b := by
  unfold cppMax
  cases StrongOrd.strongCmp a b with
  | lt => right; rfl
  | eq => left; rfl
  | gt => left; rfl

/-- `a ≤ cppMax a b` (in the `cmpLe` sense). -/
theorem cppMax_ge_left_proof (a b : T) :
    cmpLe a (cppMax a b) := by
  unfold cppMax cmpLe
  cases hab : StrongOrd.strongCmp a b with
  | lt =>
    -- max = b, need strongCmp a b ≠ .gt
    rw [hab]; decide
  | eq =>
    -- max = a, need strongCmp a a ≠ .gt
    rw [StrongOrd.cmp_refl]; decide
  | gt =>
    -- max = a, need strongCmp a a ≠ .gt
    rw [StrongOrd.cmp_refl]; decide

/-- `b ≤ cppMax a b` (in the `cmpLe` sense). -/
theorem cppMax_ge_right_proof (a b : T) :
    cmpLe b (cppMax a b) := by
  unfold cppMax cmpLe
  cases hab : StrongOrd.strongCmp a b with
  | lt =>
    -- max = b
    rw [StrongOrd.cmp_refl]; decide
  | eq =>
    -- max = a, need strongCmp b a ≠ .gt
    have := StrongOrd.flip_eq_means_eq a b hab
    rw [this]; decide
  | gt =>
    -- max = a, need strongCmp b a ≠ .gt
    rw [StrongOrd.flip_gt_means_lt a b hab]; decide

/-- `cppMax a a = a` for any `a`, given a StrongOrd. -/
theorem cppMax_self_proof (a : T) : cppMax a a = a := by
  unfold cppMax; rw [StrongOrd.cmp_refl]

/-- `cppMax` is commutative when the ordering is lawful and equality-reflecting. -/
theorem cppMax_comm_proof [StrongOrdEq T] (a b : T) :
    cppMax a b = cppMax b a := by
  unfold cppMax
  cases hab : StrongOrd.strongCmp a b with
  | lt => rw [StrongOrd.flip_lt_means_gt a b hab]
  | eq =>
    have heq := StrongOrdEq.cmp_eq_imp_eq a b hab
    subst heq; rw [StrongOrd.cmp_refl]
  | gt => rw [StrongOrd.flip_gt_means_lt a b hab]

/-! ## cppClamp properties -/

/-- The result of `cppClamp` is always one of `lo`, `hi`, or `v`. -/
theorem cppClamp_trichotomy_proof (v lo hi : T) :
    cppClamp v lo hi = lo ∨ cppClamp v lo hi = hi ∨ cppClamp v lo hi = v := by
  unfold cppClamp
  cases StrongOrd.strongCmp v lo with
  | lt => left; rfl
  | eq =>
    cases StrongOrd.strongCmp v hi with
    | lt => right; right; rfl
    | eq => right; right; rfl
    | gt => right; left; rfl
  | gt =>
    cases StrongOrd.strongCmp v hi with
    | lt => right; right; rfl
    | eq => right; right; rfl
    | gt => right; left; rfl

/-- `cppClamp` returns a value in `[lo, hi]` (given `lo ≤ hi`). -/
theorem cppClamp_in_range_proof (v lo hi : T)
    (hlohi : cmpLe lo hi) :
    cmpLe lo (cppClamp v lo hi) ∧ cmpLe (cppClamp v lo hi) hi := by
  unfold cppClamp
  cases hvlo : StrongOrd.strongCmp v lo with
  | lt =>
    -- result is lo
    exact ⟨cmpLe_refl_proof lo, hlohi⟩
  | eq =>
    -- compare v lo ≠ .lt, fallthrough to inner match
    cases hvhi : StrongOrd.strongCmp v hi with
    | lt =>
      -- result is v
      constructor
      · unfold cmpLe; rw [StrongOrd.flip_eq_means_eq v lo hvlo]; decide
      · unfold cmpLe; rw [hvhi]; decide
    | eq =>
      -- result is v
      constructor
      · unfold cmpLe; rw [StrongOrd.flip_eq_means_eq v lo hvlo]; decide
      · unfold cmpLe; rw [hvhi]; decide
    | gt =>
      -- result is hi
      exact ⟨hlohi, cmpLe_refl_proof hi⟩
  | gt =>
    cases hvhi : StrongOrd.strongCmp v hi with
    | lt =>
      -- result is v
      constructor
      · unfold cmpLe; rw [StrongOrd.flip_gt_means_lt v lo hvlo]; decide
      · unfold cmpLe; rw [hvhi]; decide
    | eq =>
      -- result is v
      constructor
      · unfold cmpLe; rw [StrongOrd.flip_gt_means_lt v lo hvlo]; decide
      · unfold cmpLe; rw [hvhi]; decide
    | gt =>
      -- result is hi
      exact ⟨hlohi, cmpLe_refl_proof hi⟩

/-- `cppClamp lo lo hi = lo` (assuming `lo ≤ hi`). -/
theorem cppClamp_lo_proof (lo hi : T)
    (h : cmpLe lo hi) : cppClamp lo lo hi = lo := by
  unfold cppClamp
  cases hll : StrongOrd.strongCmp lo lo with
  | lt => rfl
  | eq =>
    cases hlh : StrongOrd.strongCmp lo hi with
    | lt => rfl
    | eq => rfl
    | gt => exact absurd hlh h
  | gt => have := StrongOrd.cmp_refl lo; rw [this] at hll; exact absurd hll (by decide)

/-- `cppClamp hi lo hi = hi` (assuming `lo ≤ hi`). -/
theorem cppClamp_hi_proof (lo hi : T)
    (h : cmpLe lo hi) : cppClamp hi lo hi = hi := by
  unfold cppClamp
  cases hhl : StrongOrd.strongCmp hi lo with
  | lt => have := StrongOrd.flip_lt_means_gt hi lo hhl; exact absurd this h
  | eq => rw [StrongOrd.cmp_refl]
  | gt => rw [StrongOrd.cmp_refl]

/-! ## isSorted properties -/

/-- An empty list is sorted. -/
theorem isSorted_nil_proof : isSorted ([] : List T) = true := rfl

/-- A singleton list is sorted. -/
theorem isSorted_singleton_proof (a : T) : isSorted [a] = true := rfl

/-- If `a :: b :: l` is sorted, then `strongCmp a b ≠ .gt`. -/
theorem isSorted_cons_proof (a b : T) (l : List T) :
    isSorted (a :: b :: l) = true → StrongOrd.strongCmp a b ≠ Ordering.gt := by
  intro h hgt
  simp [isSorted, hgt] at h

/-- If `a :: b :: l` is sorted, then `b :: l` is sorted. -/
theorem isSorted_tail_proof (a b : T) (l : List T) :
    isSorted (a :: b :: l) = true → isSorted (b :: l) = true := by
  intro h
  simp [isSorted] at h
  cases hab : StrongOrd.strongCmp a b with
  | lt => simp [hab] at h; exact h
  | eq => simp [hab] at h; exact h
  | gt => simp [hab] at h

/-! ## minElement properties -/

/-- Helper: `foldl cppMin` yields the initial accumulator or an element of the list. -/
theorem foldl_cppMin_mem_proof (x : T) (xs : List T) :
    List.foldl (fun acc y => cppMin acc y) x xs = x ∨
    List.foldl (fun acc y => cppMin acc y) x xs ∈ xs := by
  induction xs generalizing x with
  | nil => left; rfl
  | cons y ys ih =>
    simp [List.foldl]
    have h := ih (cppMin x y)
    cases h with
    | inl heq =>
      rw [heq]
      have hcases : cppMin x y = x ∨ cppMin x y = y := by
        unfold cppMin; cases StrongOrd.strongCmp x y <;> simp
      cases hcases with
      | inl hl => left; exact hl
      | inr hr => right; left; exact hr
    | inr hmem =>
      right; right; exact hmem

/-- `minElement l` is a member of `l` when `l` is nonempty. -/
theorem minElement_mem_proof [Inhabited T] (l : List T) (hl : l ≠ []) :
    minElement l ∈ l := by
  match l, hl with
  | x :: xs, _ =>
    show List.foldl (fun acc y => cppMin acc y) x xs ∈ x :: xs
    have h := foldl_cppMin_mem_proof x xs
    cases h with
    | inl heq => rw [heq]; exact List.Mem.head xs
    | inr hmem => exact List.Mem.tail x hmem

/-- Helper: `foldl cppMin` result is ≤ the initial accumulator. -/
theorem foldl_cppMin_le_init_proof (init : T) (xs : List T) :
    cmpLe (List.foldl (fun acc y => cppMin acc y) init xs) init := by
  induction xs generalizing init with
  | nil => exact cmpLe_refl_proof init
  | cons y ys ih =>
    simp [List.foldl]
    exact cmpLe_trans_proof _ _ _ (ih (cppMin init y)) (cppMin_le_left_proof init y)

/-- Helper: `foldl cppMin` result is ≤ every element in the list. -/
theorem foldl_cppMin_le_all_proof (init : T) (xs : List T) :
    ∀ (y : T), y ∈ xs → cmpLe (List.foldl (fun acc y => cppMin acc y) init xs) y := by
  induction xs generalizing init with
  | nil => intro y hy; exact absurd hy (List.not_mem_nil y)
  | cons z zs ih =>
    intro y hy
    simp [List.foldl]
    cases hy with
    | head =>
      exact cmpLe_trans_proof _ _ _
        (foldl_cppMin_le_init_proof (cppMin init z) zs)
        (cppMin_le_right_proof init z)
    | tail _ hmem =>
      exact ih (cppMin init z) y hmem

/-- `minElement l` is ≤ every element of `l` (given `StrongOrd`). -/
theorem minElement_le_proof [Inhabited T] (l : List T) (hl : l ≠ []) :
    ∀ (x : T), x ∈ l → cmpLe (minElement l) x := by
  match l, hl with
  | z :: zs, _ =>
    intro x hx
    show cmpLe (List.foldl (fun acc y => cppMin acc y) z zs) x
    cases hx with
    | head => exact foldl_cppMin_le_init_proof z zs
    | tail _ hmem => exact foldl_cppMin_le_all_proof z zs x hmem

/-! ## Nat instance of StrongOrdEq -/

instance : StrongOrdEq Nat where
  cmp_eq_imp_eq := by
    intro a b h
    -- h : StrongOrd.strongCmp a b = .eq, which is natCmp a b = .eq
    show a = b
    have h' : natCmp a b = Ordering.eq := h
    unfold natCmp at h'
    by_cases hab : a < b
    · simp [hab] at h'
    · simp [hab] at h'
      by_cases habe : a = b
      · exact habe
      · simp [habe] at h'

end Cpp
