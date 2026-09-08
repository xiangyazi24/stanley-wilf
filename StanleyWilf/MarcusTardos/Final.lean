import StanleyWilf.MarcusTardos.ExtremalBridge
import StanleyWilf.MarcusTardos.Enumeration
import StanleyWilf.MarcusTardos.Dyadic
import StanleyWilf.Interface

/-!
# The Marcus--Tardos exponential bound

This file assembles the formalized Marcus--Tardos extremal theorem and
Klazar's enumeration argument.  Pattern-avoiding permutations inject into
finite-support zero-one matrices avoiding the corresponding permutation
matrix.  The linear weight bound controls the `2 x 2` contraction recurrence,
and the dyadic estimate supplies one explicit exponential base.

No growth-limit result is used in this construction.
-/

namespace StanleyWilf.MarcusTardos

open AnalyticCombinatorics.Ch1

variable {k n : ℕ}

/-- Send a pattern-avoiding permutation to its finite-support permutation
matrix, equipped with the corresponding matrix-avoidance proof. -/
def permutationMatrixOfAvoider (tau : Perm k) (sigma : Avoider tau n) :
    SquareAvoider (permutationMatrix tau) n :=
  ⟨permutationMatrix sigma.1, permutationMatrix_avoids_of_avoids sigma.2⟩

/-- The permutation-matrix encoding of pattern avoiders is injective. -/
theorem permutationMatrixOfAvoider_injective (tau : Perm k) :
    Function.Injective (permutationMatrixOfAvoider tau :
      Avoider tau n → SquareAvoider (permutationMatrix tau) n) := by
  intro sigma pi h
  apply Subtype.ext
  exact permutationMatrix_injective (congrArg Subtype.val h)

/-- Pattern-avoiding permutations are no more numerous than zero-one
matrices avoiding the associated permutation matrix. -/
theorem avoiderCount_le_avoidingMatrixCount (tau : Perm k) (n : ℕ) :
    avoiderCount tau n ≤ avoidingMatrixCount (permutationMatrix tau) n := by
  classical
  calc
    avoiderCount tau n = Nat.card (Avoider tau n) := by
      rw [avoiderCount, avoidanceClass, CombClass.counts]
      exact Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card (SquareAvoider (permutationMatrix tau) n) :=
      Nat.card_le_card_of_injective
        (permutationMatrixOfAvoider (n := n) tau)
        (permutationMatrixOfAvoider_injective (n := n) tau)
    _ = avoidingMatrixCount (permutationMatrix tau) n := rfl

/-- The explicit coefficient in the linear Marcus--Tardos extremal bound. -/
def marcusTardosLinearConstant (k : ℕ) : ℕ :=
  2 * k ^ 4 * (k ^ 2).choose k

/-- The formalized extremal theorem gives the linear bound required by
Klazar's contraction recurrence. -/
theorem linearAvoidingMatrixBound_permutationMatrix (tau : Perm k) :
    LinearAvoidingMatrixBound (permutationMatrix tau)
      (marcusTardosLinearConstant k) := by
  intro n A hA
  simpa only [marcusTardosLinearConstant] using
    weight_le_marcusTardos tau A hA

/-- There is at most one avoiding square matrix of side zero. -/
theorem avoidingMatrixCount_zero_le_one (tau : Perm k) :
    avoidingMatrixCount (permutationMatrix tau) 0 ≤ 1 := by
  classical
  rw [avoidingMatrixCount]
  calc
    Nat.card (SquareAvoider (permutationMatrix tau) 0) ≤
        Nat.card (ZeroOneMatrix 0 0) := Finite.card_subtype_le _
    _ = 1 := by rw [Nat.card_eq_fintype_card]; simp [ZeroOneMatrix]

/-- There are at most two avoiding zero-one matrices of side one. -/
theorem avoidingMatrixCount_one_le_two (tau : Perm k) :
    avoidingMatrixCount (permutationMatrix tau) 1 ≤ 2 := by
  classical
  rw [avoidingMatrixCount]
  calc
    Nat.card (SquareAvoider (permutationMatrix tau) 1) ≤
        Nat.card (ZeroOneMatrix 1 1) := Finite.card_subtype_le _
    _ = 2 := by rw [Nat.card_eq_fintype_card]; simp [ZeroOneMatrix]

/-- The matrix-avoidance counting sequence has the explicit uniform
natural-number exponential bound supplied by the Marcus--Tardos--Klazar
argument. -/
theorem avoidingMatrixCount_le_marcusTardosExponential (tau : Perm k) :
    ∀ n, avoidingMatrixCount (permutationMatrix tau) n ≤
      (2 * 15 ^ (2 * marcusTardosLinearConstant k)) ^ n := by
  apply count_le_uniform_exponential_of_doubling
    (fun n ↦ avoidingMatrixCount (permutationMatrix tau) n)
    (marcusTardosLinearConstant k)
  · exact avoidingMatrixCount_zero_le_one tau
  · exact avoidingMatrixCount_one_le_two tau
  · intro n
    exact avoidingMatrixCount_two_mul_le tau
      (linearAvoidingMatrixBound_permutationMatrix tau)
  · intro m n hmn
    exact avoidingMatrixCount_mono hmn tau

/-- For every finite pattern, the fully formalized Marcus--Tardos theorem
yields the exponential-bound interface used by the Stanley--Wilf growth
argument.  An explicit real base is
`2 * 15 ^ (2 * (2 * k^4 * choose (k^2) k))`. -/
theorem marcusTardosBound (tau : Perm k) :
    MarcusTardosBound tau := by
  let C : ℕ := marcusTardosLinearConstant k
  let K₀ : ℕ := 2 * 15 ^ (2 * C)
  refine ⟨(K₀ : ℝ), ?_, ?_⟩
  · have hKnat : 1 ≤ K₀ := Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
    exact_mod_cast hKnat
  · intro n
    have hnat : avoiderCount tau n ≤ K₀ ^ n :=
      (avoiderCount_le_avoidingMatrixCount tau n).trans (by
        simpa only [K₀, C] using
          avoidingMatrixCount_le_marcusTardosExponential tau n)
    exact_mod_cast hnat

/-- Compatibility form of `marcusTardosBound` for consumers which have
already separated the nontrivial-pattern case. -/
theorem marcusTardosBound_of_two_le (tau : Perm k) (_hk : 2 ≤ k) :
    MarcusTardosBound tau :=
  marcusTardosBound tau

end StanleyWilf.MarcusTardos
