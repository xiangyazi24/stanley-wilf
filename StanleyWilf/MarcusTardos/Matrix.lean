import StanleyWilf.Permutation.Basic

/-!
# Finite zero-one matrices and ordered containment

We represent a finite zero-one matrix by the finite set of positions carrying a
one.  `MatrixContains P A` is the ordered-submatrix containment relation used
by Marcus and Tardos: rows and columns may be deleted, but their order may not
be changed, and extra ones are allowed in the selected submatrix.
-/

namespace StanleyWilf.MarcusTardos

/-- A finite zero-one matrix, represented by the positions of its one-entries. -/
abbrev ZeroOneMatrix (m n : ℕ) := Finset (Fin m × Fin n)

/-- The number of one-entries in a zero-one matrix. -/
abbrev weight {m n : ℕ} (A : ZeroOneMatrix m n) : ℕ := A.card

/-- Ordered containment of zero-one matrices. -/
def MatrixContains {a b m n : ℕ} (P : ZeroOneMatrix a b)
    (A : ZeroOneMatrix m n) : Prop :=
  ∃ rows : Fin a ↪o Fin m, ∃ cols : Fin b ↪o Fin n,
    ∀ p ∈ P, (rows p.1, cols p.2) ∈ A

/-- Ordered avoidance of a zero-one matrix. -/
def MatrixAvoids {a b m n : ℕ} (P : ZeroOneMatrix a b)
    (A : ZeroOneMatrix m n) : Prop :=
  ¬ MatrixContains P A

/-- Containment is reflexive. -/
theorem matrixContains_refl {m n : ℕ} (A : ZeroOneMatrix m n) :
    MatrixContains A A := by
  refine ⟨(OrderIso.refl _).toOrderEmbedding, (OrderIso.refl _).toOrderEmbedding, ?_⟩
  simp

/-- Ordered matrix containment is transitive. -/
theorem matrixContains_trans {a b m n r s : ℕ}
    {P : ZeroOneMatrix a b} {A : ZeroOneMatrix m n} {B : ZeroOneMatrix r s}
    (hPA : MatrixContains P A) (hAB : MatrixContains A B) :
    MatrixContains P B := by
  obtain ⟨pr, pc, hP⟩ := hPA
  obtain ⟨ar, ac, hA⟩ := hAB
  refine ⟨pr.trans ar, pc.trans ac, ?_⟩
  intro p hp
  exact hA _ (hP p hp)

/-- Avoidance is inherited by ordered submatrices. -/
theorem matrixAvoids_of_contains {a b m n r s : ℕ}
    {P : ZeroOneMatrix a b} {A : ZeroOneMatrix m n} {B : ZeroOneMatrix r s}
    (hAB : MatrixContains A B) (hPB : MatrixAvoids P B) :
    MatrixAvoids P A := by
  intro hPA
  exact hPB (matrixContains_trans hPA hAB)

/-- The permutation matrix of a permutation. -/
def permutationMatrix {k : ℕ} (τ : Perm k) : ZeroOneMatrix k k :=
  Finset.univ.map ⟨fun i ↦ (i, τ i), fun _ _ h ↦ congrArg Prod.fst h⟩

@[simp]
theorem mem_permutationMatrix {k : ℕ} (τ : Perm k) (i j : Fin k) :
    (i, j) ∈ permutationMatrix τ ↔ j = τ i := by
  simp [permutationMatrix, eq_comm]

@[simp]
theorem weight_permutationMatrix {k : ℕ} (τ : Perm k) :
    weight (permutationMatrix τ) = k := by
  simp [permutationMatrix]

end StanleyWilf.MarcusTardos
