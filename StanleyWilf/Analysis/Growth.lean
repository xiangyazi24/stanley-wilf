import StanleyWilf.Counting
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite growth from supermultiplicativity

The exponential upper bound is a hypothesis. Fekete is imported from mathlib,
not reintroduced as an axiom. Positivity is explicit, so logarithms are only
used on positive values. The zero index has totalized inverse `0⁻¹ = 0` and
therefore causes no division-domain side condition.
-/

namespace StanleyWilf

open Filter Topology

/-- A finite exponential upper bound, with a base at least one. -/
def ExponentialBound (a : ℕ → ℕ) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ n, (a n : ℝ) ≤ K ^ n

/-- The positive-index terms are exactly the usual nth roots. -/
noncomputable def growthRoot (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ ((n : ℝ)⁻¹)

theorem neg_log_subadditive {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hsuper : Supermultiplicative a) :
    Subadditive (fun n => -Real.log (a n : ℝ)) := by
  intro m n
  have hm : 0 < (a m : ℝ) := by exact_mod_cast hpos m
  have hn : 0 < (a n : ℝ) := by exact_mod_cast hpos n
  have hmul : (a m : ℝ) * (a n : ℝ) ≤ (a (m + n) : ℝ) := by
    exact_mod_cast hsuper m n
  have hlog := Real.log_le_log (mul_pos hm hn) hmul
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hn)] at hlog
  linarith

/-- An exponential bound is precisely enough for the lower-bound input to Fekete. -/
theorem neg_log_div_bddBelow {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hbound : ExponentialBound a) :
    BddBelow (Set.range (fun n : ℕ => -Real.log (a n : ℝ) / (n : ℝ))) := by
  obtain ⟨K, hK, hupper⟩ := hbound
  refine ⟨-Real.log K, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, div_zero]
    exact neg_nonpos.mpr (Real.log_nonneg hK)
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have ha : 0 < (a n : ℝ) := by exact_mod_cast hpos n
    have hlog : Real.log (a n : ℝ) ≤ (n : ℝ) * Real.log K := by
      calc
        Real.log (a n : ℝ) ≤ Real.log (K ^ n) := Real.log_le_log ha (hupper n)
        _ = (n : ℝ) * Real.log K := Real.log_pow K n
    apply (le_div_iff₀ hnR).2
    nlinarith

/-- A strictly positive supermultiplicative sequence with an exponential bound
has a positive, finite real growth limit. This is the reusable analytic engine,
not yet the concrete Stanley–Wilf theorem for pattern avoiders. -/
theorem exists_growthRate {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hsuper : Supermultiplicative a)
    (hbound : ExponentialBound a) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (growthRoot a) atTop (𝓝 L) := by
  have hsub := neg_log_subadditive hpos hsuper
  have hbdd := neg_log_div_bddBelow hpos hbound
  have ht := hsub.tendsto_lim hbdd
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (-(-Real.log (a n : ℝ) / (n : ℝ))))
      atTop (𝓝 (Real.exp (-hsub.lim))) :=
    Real.continuous_exp.continuousAt.tendsto.comp ht.neg
  refine ⟨Real.exp (-hsub.lim), Real.exp_pos _, ?_⟩
  have hroot : growthRoot a =
      (fun n : ℕ => Real.exp (-(-Real.log (a n : ℝ) / (n : ℝ)))) := by
    funext n
    have ha : 0 < (a n : ℝ) := by exact_mod_cast hpos n
    simp [growthRoot, Real.rpow_def_of_pos ha, div_eq_mul_inv]
  rw [hroot]
  exact hexp

end StanleyWilf
