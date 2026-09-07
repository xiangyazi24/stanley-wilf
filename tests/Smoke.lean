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
