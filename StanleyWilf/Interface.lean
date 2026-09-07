import StanleyWilf.Permutation.Basic
import StanleyWilf.Analysis.Growth

/-!
# The concrete target and its explicit inputs

`MarcusTardosBound` is only a definition of a proposition. No inhabitant is
postulated. `growthTarget_of_product` is deliberately named to show its
remaining input: a constructor on the actual avoidance class.
-/

namespace StanleyWilf

open Filter Topology

variable {k : ℕ}

/-- The established mathematical theorem's exponential-bound interface.
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

end StanleyWilf
