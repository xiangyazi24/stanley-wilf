import StanleyWilf.Symbolic.AvoidanceSequence
import StanleyWilf.Interface

/-!
# A Stanley–Wilf growth endpoint genuinely routed through the symbolic method

The first-component bijection gives a nonnegative convolution. That convolution
proves supermultiplicativity, which supplies the analytic Fekete backend.
Neither `GradedProduct` nor `avoidanceProduct` is used by this proof.
Marcus–Tardos remains the single explicit exponential-bound input.
-/

namespace StanleyWilf

variable {k : ℕ}

/-- The symbolic route, with the empty and singleton forbidden patterns handled
before logarithms. This is source awaiting compilation, not a kernel certificate. -/
theorem stanleyWilf_symbolic (τ : Perm k) (hMT : MarcusTardosBound τ) : GrowthTarget τ := by
  by_cases hk : k ≤ 1
  · exact growthTarget_of_length_le_one τ hk
  · have hk0 : 0 < k := by omega
    have hsuper := avoiderCount_supermultiplicative_symbolic τ hk0
    have h0 : 1 ≤ avoiderCount τ 0 := avoiderCount_pos_of_lt τ hk0
    have h1 : 1 ≤ avoiderCount τ 1 := avoiderCount_pos_of_lt τ (by omega)
    have hpos := one_le_all_of_supermultiplicative hsuper h0 h1
    obtain ⟨L, hL, ht⟩ := exists_growthRate
      (fun n => Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos n)) hsuper hMT
    exact ⟨L, le_of_lt hL, ht⟩

end StanleyWilf
