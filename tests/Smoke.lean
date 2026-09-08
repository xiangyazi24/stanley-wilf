import StanleyWilf

open Filter Topology StanleyWilf

example : Supermultiplicative (fun n : ℕ => 2 ^ n) := by
  intro m n
  simp [pow_add]

example : Avoids (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1)) :=
  avoids_of_size_lt _ _ (by decide)

example : Function.Injective
    (fun p : Perm 2 × Perm 3 => directSum p.1 p.2) := directSum_injective 2 3

example : Function.Injective
    (fun p : Perm 2 × Perm 3 => skewSum p.1 p.2) := skewSum_injective 2 3

example : ∃ L : ℝ, 0 < L ∧ Tendsto (growthRoot (fun _ => 1)) atTop (𝓝 L) := by
  apply exists_growthRate
  · intro n
    decide
  · intro m n
    simp
  · exact ⟨1, by norm_num, by intro n; simp⟩

-- The concrete avoidance sequence has no externally supplied constructor.
example {k : ℕ} (τ : Perm k) : Supermultiplicative (avoiderCount τ) :=
  avoiderCount_supermultiplicative τ

example {k m n : ℕ} (τ : Perm k) (σ : Perm m) (π : Perm n)
    (hτ : SumIndecomposable τ) (hσ : Avoids τ σ) (hπ : Avoids τ π) :
    Avoids τ (directSum σ π) := avoids_directSum hτ hσ hπ

example {k m n : ℕ} (τ : Perm k) (σ : Perm m) (π : Perm n)
    (hτ : SkewIndecomposable τ) (hσ : Avoids τ σ) (hπ : Avoids τ π) :
    Avoids τ (skewSum σ π) := avoids_skewSum hτ hσ hπ

-- This statement requires neither a constructor nor a nontrivial-length input.
example {k : ℕ} (τ : Perm k) (hMT : MarcusTardosBound τ) : GrowthTarget τ :=
  stanleyWilf_of_marcusTardos τ hMT

example (τ : Perm 1) : GrowthTarget τ :=
  growthTarget_of_length_le_one τ (by decide)

example (τ : Perm 0) : GrowthTarget τ :=
  growthTarget_of_length_le_one τ (by decide)

-- Concrete first components, including the full-length boundary.
example {n : ℕ} (σ : Perm n) (hn : 0 < n) :
    IsFirstSumBoundary σ (firstSumBoundary σ hn) := firstSumBoundary_spec σ hn

example {n c : ℕ} (σ : Perm n) (h : SumBoundary σ c) :
    castPerm (show c + (n-c) = n by have := h.1; omega)
      (directSum (prefixPerm σ h) (suffixPerm σ h)) = σ :=
  reconstruct_prefix_suffix σ h

example {n c : ℕ} (σ : Perm n) (h : IsFirstSumBoundary σ c) :
    SumIndecomposable (prefixPerm σ h.2.1) := prefixPerm_indecomposable_of_first σ h

example : (complement (Equiv.refl (Fin 3)) (0 : Fin 3)).val = 2 := by decide

noncomputable example {k : ℕ} (τ : Perm k) (hk : 0 < k) :
    SequenceSpecification (avoidanceClass τ) (indecomposableAtomClass τ) :=
  avoidanceSequenceSpecification τ hk

example {k : ℕ} (τ : Perm k) (hk : 0 < k) :
    (avoidanceClass τ).ogf * (1 - (indecomposableAtomClass τ).ogf) = 1 :=
  avoidance_ogf_mul_one_sub τ hk

-- The singleton pattern's class is epsilon, not a positive-size logarithm case.
noncomputable example (τ : Perm 1) :
    SequenceSpecification (avoidanceClass τ) (indecomposableAtomClass τ) :=
  avoidanceSequenceSpecification τ (by decide)

-- The relative endpoint keeps the bound explicit for modular auditing.
example {k : ℕ} (τ : Perm k) (hMT : MarcusTardosBound τ) : GrowthTarget τ :=
  stanleyWilf_symbolic_of_marcusTardos τ hMT

-- The public symbolic endpoint has no mathematical hypotheses.
example {k : ℕ} (τ : Perm k) : GrowthTarget τ :=
  stanleyWilf_symbolic τ

example {k : ℕ} (τ : Perm k) : GrowthTarget τ :=
  stanleyWilf τ
