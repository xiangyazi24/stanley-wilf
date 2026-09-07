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
