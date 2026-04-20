import DeanLean.Cpp.Code.Vector

namespace Cpp.Vector

variable {T : Type}

theorem size_empty_proof : (Vector.empty : Vector T).size = 0 := by
  simp [empty, size]

theorem size_push_back_proof (v : Vector T) (x : T) :
    (v.push_back x).size = v.size + 1 := by
  simp [push_back, size, Array.size_push]

theorem size_pop_back_proof (v : Vector T) (_h : v.size > 0) :
    (v.pop_back).size = v.size - 1 := by
  simp [pop_back, size, Array.size_pop]

theorem get_push_back_last_proof (v : Vector T) (x : T) :
    (v.push_back x).get ⟨v.size, by simp [push_back, size, Array.size_push]⟩ = x := by
  simp [push_back, get, size, Array.getElem_push_eq]

theorem size_clear_proof (v : Vector T) : (v.clear).size = 0 := by
  simp [clear, size]

theorem isEmpty_iff_size_zero_proof (v : Vector T) :
    v.isEmpty = true ↔ v.size = 0 := by
  simp [isEmpty, size, Array.isEmpty]

theorem push_back_pop_back_proof (v : Vector T) (h : v.size > 0) :
    (v.pop_back).push_back (v.back h) = v := by
  simp only [push_back, pop_back, back, size]
  congr 1
  have hd : 0 < v.data.size := h
  ext i hi1 hi2
  · simp [Array.size_push, Array.size_pop]; omega
  · simp [Array.size_push, Array.size_pop] at hi1 hi2
    by_cases hlt : i < v.data.size - 1
    · simp [Array.getElem_push, Array.getElem_pop, Array.size_pop, hlt]
    · have : i = v.data.size - 1 := by omega
      subst this
      simp [Array.getElem_push, Array.size_pop, hlt]

end Cpp.Vector
