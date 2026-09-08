import StanleyWilf.MarcusTardos.Final
import StanleyWilf.Symbolic.Growth

/-!
# Smoke tests for the Marcus--Tardos layer

These consumers check the semantic bridge between permutation patterns and
ordered zero-one matrices and the concrete extremal estimate.  The examples
at pattern sizes zero, one, and two guard the boundary conventions used by the
unconditional Stanley--Wilf endpoint.
-/

open StanleyWilf

namespace StanleyWilf.MarcusTardos

/-! The permutation-pattern/matrix-containment bridge is usable in both directions. -/

example {k n : ℕ} {tau : Perm k} {sigma : Perm n} (h : Contains tau sigma) :
    MatrixContains (permutationMatrix tau) (permutationMatrix sigma) :=
  permutationMatrix_contains_of_contains h

example {k n : ℕ} {tau : Perm k} {sigma : Perm n}
    (h : MatrixContains (permutationMatrix tau) (permutationMatrix sigma)) :
    Contains tau sigma :=
  contains_of_permutationMatrix_contains h

example {k n : ℕ} {tau : Perm k} {sigma : Perm n} (h : Avoids tau sigma) :
    MatrixAvoids (permutationMatrix tau) (permutationMatrix sigma) :=
  avoids_iff_permutationMatrix_avoids.mp h

example {k n : ℕ} {tau : Perm k} {sigma : Perm n}
    (h : MatrixAvoids (permutationMatrix tau) (permutationMatrix sigma)) :
    Avoids tau sigma :=
  avoids_iff_permutationMatrix_avoids.mpr h

/-! Permutation matrices preserve identity and have exactly one entry per row. -/

example {n : ℕ} :
    Function.Injective (permutationMatrix : Perm n → ZeroOneMatrix n n) :=
  permutationMatrix_injective

example {n : ℕ} (sigma : Perm n) : weight (permutationMatrix sigma) = n :=
  weight_permutationMatrix sigma

/-! Boundary semantics for patterns of sizes zero, one, and two. -/

example : weight (permutationMatrix (Equiv.refl (Fin 0))) = 0 := by simp

example : Contains (Equiv.refl (Fin 0)) (Equiv.refl (Fin 0)) :=
  contains_refl _

example : ¬ Avoids (Equiv.refl (Fin 0)) (Equiv.refl (Fin 0)) := by
  exact fun h ↦ h (contains_refl _)

example : weight (permutationMatrix (Equiv.refl (Fin 1))) = 1 := by simp

example : Contains (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) :=
  contains_refl _

example : ¬ Avoids (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) := by
  exact fun h ↦ h (contains_refl _)

example : weight (permutationMatrix (Equiv.refl (Fin 2))) = 2 := by simp

example : Avoids (Equiv.swap (0 : Fin 2) 1) (Equiv.refl (Fin 2)) := by
  rintro ⟨occ⟩
  have hpos : occ.position (0 : Fin 2) < occ.position (1 : Fin 2) :=
    occ.position.strictMono (by decide)
  have hvalues := (occ.pattern (0 : Fin 2) (1 : Fin 2)).mpr hpos
  simp at hvalues

example : MatrixAvoids
    (permutationMatrix (Equiv.swap (0 : Fin 2) 1))
    (permutationMatrix (Equiv.refl (Fin 2))) := by
  apply permutationMatrix_avoids_of_avoids
  rintro ⟨occ⟩
  have hpos : occ.position (0 : Fin 2) < occ.position (1 : Fin 2) :=
    occ.position.strictMono (by decide)
  have hvalues := (occ.pattern (0 : Fin 2) (1 : Fin 2)).mpr hpos
  simp at hvalues

/-! The extremal, enumerative, and final endpoints are usable without hidden inputs. -/

example {k n : ℕ} (tau : Perm k) (A : ZeroOneMatrix n n)
    (hA : MatrixAvoids (permutationMatrix tau) A) :
    weight A ≤ 2 * k ^ 4 * (k ^ 2).choose k * n :=
  weight_le_marcusTardos tau A hA

example {k : ℕ} (tau : Perm k) : MarcusTardosBound tau :=
  marcusTardosBound tau

example {k : ℕ} (tau : Perm k) : GrowthTarget tau :=
  StanleyWilf.stanleyWilf tau

end StanleyWilf.MarcusTardos
