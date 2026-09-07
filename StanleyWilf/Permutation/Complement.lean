import StanleyWilf.Permutation.Cuts
import StanleyWilf.Permutation.BlockSum

/-! # Value complement and the direct/skew symmetry -/

namespace StanleyWilf

variable {k m n : ℕ}

/-- Reverse the order of the value alphabet, without changing any position. -/
def reverseValueIndex (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by have := i.isLt; omega⟩

@[simp] theorem reverseValueIndex_val (i : Fin n) :
    (reverseValueIndex i).val = n - 1 - i.val := rfl

@[simp] theorem reverseValueIndex_twice (i : Fin n) :
    reverseValueIndex (reverseValueIndex i) = i := by
  apply Fin.ext
  change n - 1 - (n - 1 - i.val) = i.val
  have := i.isLt
  omega

def complement (σ : Perm n) : Perm n where
  toFun i := reverseValueIndex (σ i)
  invFun i := σ.symm (reverseValueIndex i)
  left_inv i := by
    change σ.symm (reverseValueIndex (reverseValueIndex (σ i))) = i
    simp
  right_inv i := by
    change reverseValueIndex (σ (σ.symm (reverseValueIndex i))) = i
    simp

@[simp] theorem complement_val (σ : Perm n) (i : Fin n) :
    (complement σ i).val = n - 1 - (σ i).val := rfl

@[simp] theorem complement_twice (σ : Perm n) : complement (complement σ) = σ := by
  apply Equiv.ext
  intro i
  exact reverseValueIndex_twice (σ i)

theorem complement_lt_iff (σ : Perm n) (i j : Fin n) :
    complement σ i < complement σ j ↔ σ j < σ i := by
  change n - 1 - (σ i).val < n - 1 - (σ j).val ↔ (σ j).val < (σ i).val
  have hi := (σ i).isLt
  have hj := (σ j).isLt
  omega

/-- Complement both the pattern and the ambient permutation. -/
def Occurrence.complement {τ : Perm k} {σ : Perm n} (e : Occurrence τ σ) :
    Occurrence (complement τ) (complement σ) where
  position := e.position
  pattern i j := (complement_lt_iff τ i j).trans
    ((e.pattern j i).trans (complement_lt_iff σ (e.position i) (e.position j)).symm)

theorem contains_complement_iff (τ : Perm k) (σ : Perm n) :
    Contains (complement τ) (complement σ) ↔ Contains τ σ := by
  constructor
  · rintro ⟨e⟩
    have e' := e.complement
    rw [complement_twice, complement_twice] at e'
    exact ⟨e'⟩
  · rintro ⟨e⟩
    exact ⟨e.complement⟩

theorem avoids_complement_iff (τ : Perm k) (σ : Perm n) :
    Avoids (complement τ) (complement σ) ↔ Avoids τ σ :=
  not_congr (contains_complement_iff τ σ)

theorem isSumCut_complement_iff (σ : Perm n) (c : ℕ) :
    IsSumCut (complement σ) c ↔ IsSkewCut σ c := by
  simp only [IsSumCut, IsSkewCut, complement_lt_iff]

theorem isSkewCut_complement_iff (σ : Perm n) (c : ℕ) :
    IsSkewCut (complement σ) c ↔ IsSumCut σ c := by
  simp only [IsSumCut, IsSkewCut, complement_lt_iff]

theorem sumIndecomposable_complement_iff (σ : Perm n) :
    SumIndecomposable (complement σ) ↔ SkewIndecomposable σ := by
  simp only [SumIndecomposable, SumDecomposable, SkewIndecomposable,
    SkewDecomposable, isSumCut_complement_iff]

theorem skewIndecomposable_complement_iff (σ : Perm n) :
    SkewIndecomposable (complement σ) ↔ SumIndecomposable σ := by
  simp only [SumIndecomposable, SumDecomposable, SkewIndecomposable,
    SkewDecomposable, isSkewCut_complement_iff]

/-- This is the actual skew-sum operation already used by the growth proof. -/
theorem complement_directSum (σ : Perm m) (π : Perm n) :
    complement (directSum σ π) = skewSum (complement σ) (complement π) := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · rw [complement_val, directSum_castAdd_val, skewSum_castAdd_val, complement_val]
    have hi := (σ i).isLt
    omega
  · rw [complement_val, directSum_natAdd_val, skewSum_natAdd_val, complement_val]
    have hj := (π j).isLt
    omega

end StanleyWilf
