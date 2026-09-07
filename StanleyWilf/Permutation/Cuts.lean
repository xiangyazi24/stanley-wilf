import StanleyWilf.Permutation.Basic

/-!
# Direct and skew cuts

A cut uses a nonempty initial block and a nonempty final block. For a
permutation, separating all values across the cut is the usual direct/skew
sum condition. This file proves incompatibility directly from the first and
last positions; no existence of a decomposition is assumed.
-/

namespace StanleyWilf

variable {n : ℕ}

def IsSumCut (σ : Perm n) (k : ℕ) : Prop :=
  0 < k ∧ k < n ∧
    ∀ i j : Fin n, i.val < k → k ≤ j.val → σ i < σ j

def IsSkewCut (σ : Perm n) (k : ℕ) : Prop :=
  0 < k ∧ k < n ∧
    ∀ i j : Fin n, i.val < k → k ≤ j.val → σ j < σ i

def SumDecomposable (σ : Perm n) : Prop := ∃ k, IsSumCut σ k

def SkewDecomposable (σ : Perm n) : Prop := ∃ k, IsSkewCut σ k

def SumIndecomposable (σ : Perm n) : Prop := ¬ SumDecomposable σ

def SkewIndecomposable (σ : Perm n) : Prop := ¬ SkewDecomposable σ

/-- A permutation cannot admit both kinds of nontrivial cut. -/
theorem not_sum_and_skew_decomposable (σ : Perm n) :
    ¬ (SumDecomposable σ ∧ SkewDecomposable σ) := by
  rintro ⟨⟨k, hk0, hkn, hsum⟩, ⟨l, hl0, hln, hskew⟩⟩
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have h₁ : σ first < σ last :=
    hsum first last (by dsimp [first]; omega) (by dsimp [last]; omega)
  have h₂ : σ last < σ first :=
    hskew first last (by dsimp [first]; omega) (by dsimp [last]; omega)
  exact lt_asymm h₁ h₂

/-- Choose an operation for which the forbidden pattern is indecomposable. -/
theorem sumIndecomposable_or_skewIndecomposable (σ : Perm n) :
    SumIndecomposable σ ∨ SkewIndecomposable σ := by
  classical
  by_cases h : SumDecomposable σ
  · exact Or.inr (fun h' => not_sum_and_skew_decomposable σ ⟨h, h'⟩)
  · exact Or.inl h

end StanleyWilf
