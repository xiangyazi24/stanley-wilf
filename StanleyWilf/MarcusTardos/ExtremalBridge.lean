import StanleyWilf.MarcusTardos.PermutationMatrix
import StanleyWilf.ForbiddenMatrix.PermutationPatterns

/-!
# Bridge to the Marcus--Tardos extremal matrix theorem

The extremal proof uses matrices as predicates, while the enumerative layer
uses finite supports.  This file proves that the two containment relations and
their notions of density agree.  It then specializes the formalized
Marcus--Tardos bound to finite-support permutation matrices.
-/

namespace StanleyWilf.MarcusTardos

variable {a b m n k : ℕ}

open StanleyWilf.ForbiddenMatrix

/-- The predicate-valued matrix represented by a finite support. -/
def asPredicate (A : ZeroOneMatrix m n) : Fin m → Fin n → Prop :=
  fun i j ↦ (i, j) ∈ A

/-- The finite-support and predicate formulations of ordered containment agree. -/
theorem matrixContains_iff_forbiddenContains
    (P : ZeroOneMatrix a b) (A : ZeroOneMatrix m n) :
    MatrixContains P A ↔
      StanleyWilf.ForbiddenMatrix.Contains (asPredicate P) (asPredicate A) := by
  constructor
  · rintro ⟨rows, cols, h⟩
    exact ⟨rows, rows.strictMono, cols, cols.strictMono, fun i j hij ↦ h (i, j) hij⟩
  · rintro ⟨rows, hrows, cols, hcols, h⟩
    exact ⟨OrderEmbedding.ofStrictMono rows hrows,
      OrderEmbedding.ofStrictMono cols hcols, fun p hp ↦ h p.1 p.2 hp⟩

/-- Predicate density is the cardinality of the finite support. -/
theorem density_asPredicate (A : ZeroOneMatrix n n) :
    density (asPredicate A) = weight A := by
  classical
  rw [density_def]
  simp [asPredicate, Finset.filter_mem_eq_inter]

/-- Our permutation matrix is extensionally the pattern predicate used by the
formalized extremal theorem. -/
theorem asPredicate_permutationMatrix (τ : Perm k) :
    asPredicate (permutationMatrix τ) = PermPattern τ := by
  funext i j
  simp [asPredicate, PermPattern, eq_comm]

/-- Explicit Marcus--Tardos linear bound for every finite-support square
matrix avoiding a fixed permutation matrix. -/
theorem weight_le_marcusTardos (τ : Perm k) (A : ZeroOneMatrix n n)
    (hA : MatrixAvoids (permutationMatrix τ) A) :
    weight A ≤ 2 * k ^ 4 * (k ^ 2).choose k * n := by
  rw [← density_asPredicate A]
  have havoid : ¬ StanleyWilf.ForbiddenMatrix.Contains
      (PermPattern τ) (asPredicate A) := by
    intro hcontains
    apply hA
    exact (matrixContains_iff_forbiddenContains _ _).mpr (by
      simpa only [asPredicate_permutationMatrix] using hcontains)
  calc
    density (asPredicate A) ≤ ex (PermPattern τ) n :=
      density_le_ex_of_not_contains (asPredicate A) havoid
    _ ≤ 2 * k ^ 4 * (k ^ 2).choose k * n := ex_permPattern_le τ n

end StanleyWilf.MarcusTardos
