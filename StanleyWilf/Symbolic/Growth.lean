import StanleyWilf.Symbolic.AvoidanceSequence
import StanleyWilf.MarcusTardos.Final

/-!
# A Stanley–Wilf growth endpoint genuinely routed through the symbolic method

The first-component bijection gives a nonnegative convolution. That convolution
proves supermultiplicativity, which supplies the analytic Fekete backend.
Neither `GradedProduct` nor `avoidanceProduct` is used by this proof.  The
relative theorem keeps the exponential bound explicit; the final theorem
supplies it from the formalized Marcus--Tardos--Klazar argument.
-/

namespace StanleyWilf

variable {k : ℕ}

/-- The relative symbolic route, with the empty and singleton forbidden
patterns handled before logarithms. -/
theorem stanleyWilf_symbolic_of_marcusTardos
    (τ : Perm k) (hMT : MarcusTardosBound τ) : GrowthTarget τ := by
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

/-- The unconditional Stanley--Wilf growth-limit theorem, proved through the
symbolic first-component recurrence and the formalized Marcus--Tardos bound. -/
theorem stanleyWilf_symbolic (τ : Perm k) : GrowthTarget τ :=
  stanleyWilf_symbolic_of_marcusTardos τ
    (MarcusTardos.marcusTardosBound τ)

/-- Short public name for the unconditional Stanley--Wilf theorem. -/
theorem stanleyWilf (τ : Perm k) : GrowthTarget τ :=
  stanleyWilf_symbolic τ

end StanleyWilf
