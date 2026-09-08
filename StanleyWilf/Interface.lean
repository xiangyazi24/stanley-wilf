import StanleyWilf.Permutation.AvoidanceProduct
import StanleyWilf.Permutation.SmallPatterns
import StanleyWilf.Analysis.Growth

/-!
# The concrete target and relative assembly lemmas

`MarcusTardosBound` is only a definition of a proposition. No inhabitant is
postulated in this module. `growthTarget_of_product` remains a reusable
assembly lemma, while `stanleyWilf_of_marcusTardos` supplies the actual
combinatorial constructor and handles zero/one-element patterns. The producer
of `MarcusTardosBound` is proved later in `MarcusTardos.Final`.
-/

namespace StanleyWilf

open Filter Topology

variable {k : ℕ}

/-- The exponential-bound interface used by the relative assembly lemmas.
There is no axiom asserting that this proposition holds. -/
def MarcusTardosBound (τ : Perm k) : Prop :=
  ExponentialBound (avoiderCount τ)

/-- The desired finite growth-limit statement, also covering limit zero. -/
def GrowthTarget (τ : Perm k) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ Tendsto (growthRoot (avoiderCount τ)) atTop (𝓝 L)

/-- Below the pattern length, the identity permutation supplies an avoider. -/
theorem avoiderCount_pos_of_lt (τ : Perm k) {n : ℕ} (h : n < k) :
    0 < avoiderCount τ n := by
  classical
  change 0 < Fintype.card (Avoider τ n)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨Equiv.refl _, avoids_of_size_lt τ (Equiv.refl _) h⟩⟩

/-- Assemble the nontrivial-pattern target once the concrete constructor and
Marcus–Tardos bound are supplied. Neither input is hidden. -/
theorem growthTarget_of_product (τ : Perm k) (hk : 2 ≤ k)
    (P : GradedProduct (avoidanceClass τ)) (hMT : MarcusTardosBound τ) :
    GrowthTarget τ := by
  have h0 : 1 ≤ avoiderCount τ 0 :=
    Nat.succ_le_iff.mpr (avoiderCount_pos_of_lt τ (by omega))
  have h1 : 1 ≤ avoiderCount τ 1 :=
    Nat.succ_le_iff.mpr (avoiderCount_pos_of_lt τ (by omega))
  have hsuper : Supermultiplicative (avoiderCount τ) := P.counts_supermultiplicative
  have hpos : ∀ n, 0 < avoiderCount τ n := by
    intro n
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (one_le_all_of_supermultiplicative hsuper h0 h1 n)
  obtain ⟨L, hL, ht⟩ := exists_growthRate hpos hsuper hMT
  exact ⟨L, le_of_lt hL, ht⟩

/-- The actual avoidance constructor discharges the former product hypothesis. -/
theorem growthTarget_of_marcusTardos_nontrivial (τ : Perm k) (hk : 2 ≤ k)
    (hMT : MarcusTardosBound τ) : GrowthTarget τ :=
  growthTarget_of_product τ hk (avoidanceProduct τ) hMT

/-- Degenerate patterns have root limit zero, without any exponential-bound input. -/
theorem growthTarget_of_length_le_one (τ : Perm k) (hk : k ≤ 1) : GrowthTarget τ := by
  refine ⟨0, le_refl _, ?_⟩
  have hroot : growthRoot (avoiderCount τ) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    have hexp : (n : ℝ)⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr hnR)
    rw [growthRoot, avoiderCount_eq_zero_of_length_le_one τ hk hn0, Nat.cast_zero]
    exact Real.zero_rpow hexp
  exact tendsto_const_nhds.congr' hroot.symm

/-- The relative Stanley–Wilf theorem for the concrete pattern-counting sequence.
Its only hypothesis is the explicitly quantified Marcus–Tardos bound, which is
discharged by `MarcusTardos.marcusTardosBound` at the public endpoint. -/
theorem stanleyWilf_of_marcusTardos (τ : Perm k) (hMT : MarcusTardosBound τ) :
    GrowthTarget τ := by
  by_cases hk : 2 ≤ k
  · exact growthTarget_of_marcusTardos_nontrivial τ hk hMT
  · exact growthTarget_of_length_le_one τ (by omega)

end StanleyWilf
