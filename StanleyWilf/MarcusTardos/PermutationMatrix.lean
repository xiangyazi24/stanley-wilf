import StanleyWilf.MarcusTardos.Matrix

/-!
# Permutation patterns as ordered permutation matrices

This file proves the direction needed by the Marcus--Tardos counting reduction:
matrix containment between permutation matrices produces a classical
permutation-pattern occurrence.
-/

namespace StanleyWilf.MarcusTardos

variable {k n : ℕ}

/-- A permutation is determined by the support of its permutation matrix. -/
theorem permutationMatrix_injective :
    Function.Injective (permutationMatrix : Perm n → ZeroOneMatrix n n) := by
  intro σ π h
  apply Equiv.ext
  intro i
  have hi : (i, σ i) ∈ permutationMatrix σ := by simp
  rw [h] at hi
  simpa using hi

/-- Ordered containment of permutation matrices yields pattern containment. -/
theorem contains_of_permutationMatrix_contains {τ : Perm k} {σ : Perm n}
    (h : MatrixContains (permutationMatrix τ) (permutationMatrix σ)) :
    Contains τ σ := by
  obtain ⟨rows, cols, hmem⟩ := h
  have hentry : ∀ i : Fin k, cols (τ i) = σ (rows i) := by
    intro i
    have hpoint := hmem (i, τ i) (by simp)
    simpa using hpoint
  refine ⟨⟨rows, ?_⟩⟩
  intro i j
  rw [← hentry i, ← hentry j]
  exact cols.lt_iff_lt.symm

/-- A pattern occurrence yields ordered containment of permutation matrices. -/
theorem permutationMatrix_contains_of_contains {τ : Perm k} {σ : Perm n}
    (h : Contains τ σ) :
    MatrixContains (permutationMatrix τ) (permutationMatrix σ) := by
  obtain ⟨occ⟩ := h
  let valueMap : Fin k → Fin n := fun x ↦ σ (occ.position (τ.symm x))
  have hvalueMap : StrictMono valueMap := by
    intro x y hxy
    have hpattern := (occ.pattern (τ.symm x) (τ.symm y)).mp
    exact hpattern (by simpa using hxy)
  let cols : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono valueMap hvalueMap
  refine ⟨occ.position, cols, ?_⟩
  intro p hp
  have hp' : p.2 = τ p.1 := (mem_permutationMatrix τ p.1 p.2).mp hp
  rw [hp']
  simp [cols, valueMap]

/-- Classical pattern containment is exactly ordered permutation-matrix containment. -/
theorem contains_iff_permutationMatrix_contains {τ : Perm k} {σ : Perm n} :
    Contains τ σ ↔ MatrixContains (permutationMatrix τ) (permutationMatrix σ) :=
  ⟨permutationMatrix_contains_of_contains, contains_of_permutationMatrix_contains⟩

/-- Classical avoidance is exactly avoidance of the corresponding permutation matrix. -/
theorem avoids_iff_permutationMatrix_avoids {τ : Perm k} {σ : Perm n} :
    Avoids τ σ ↔ MatrixAvoids (permutationMatrix τ) (permutationMatrix σ) := by
  simp only [Avoids, MatrixAvoids, contains_iff_permutationMatrix_contains]

/-- Pattern avoidance implies avoidance of the corresponding permutation matrix. -/
theorem permutationMatrix_avoids_of_avoids {τ : Perm k} {σ : Perm n}
    (h : Avoids τ σ) :
    MatrixAvoids (permutationMatrix τ) (permutationMatrix σ) := by
  intro hcontains
  exact h (contains_of_permutationMatrix_contains hcontains)

end StanleyWilf.MarcusTardos
