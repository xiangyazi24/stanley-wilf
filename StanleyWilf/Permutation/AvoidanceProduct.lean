import StanleyWilf.Permutation.Closure
import StanleyWilf.Counting

/-!
# The concrete graded constructor on avoiders

These are implementations of `GradedProduct`, not new hypotheses asserting
that the avoidance class has one. Fixed-size injectivity is inherited from
the actual block permutations, and closure is proved in `Closure.lean`.
-/

namespace StanleyWilf

variable {k : ℕ}

/-- Direct sum restricted to the subtype of avoiders. -/
noncomputable def directAvoidanceProduct (τ : Perm k) (hτ : SumIndecomposable τ) :
    GradedProduct (avoidanceClass τ) where
  join _ _ p := ⟨directSum p.1.val p.2.val, avoids_directSum hτ p.1.property p.2.property⟩
  injective m n := by
    intro p q h
    have hv : directSum p.1.val p.2.val = directSum q.1.val q.2.val :=
      congrArg Subtype.val h
    have hpq := directSum_injective m n hv
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpq)
    · exact Subtype.ext (congrArg Prod.snd hpq)

/-- Skew sum restricted to the subtype of avoiders. -/
noncomputable def skewAvoidanceProduct (τ : Perm k) (hτ : SkewIndecomposable τ) :
    GradedProduct (avoidanceClass τ) where
  join _ _ p := ⟨skewSum p.1.val p.2.val, avoids_skewSum hτ p.1.property p.2.property⟩
  injective m n := by
    intro p q h
    have hv : skewSum p.1.val p.2.val = skewSum q.1.val q.2.val :=
      congrArg Subtype.val h
    have hpq := skewSum_injective m n hv
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpq)
    · exact Subtype.ext (congrArg Prod.snd hpq)

/-- Every single-pattern avoidance class has an injective graded constructor.
The operation depends only on the forbidden pattern, not on the input sizes. -/
noncomputable def avoidanceProduct (τ : Perm k) : GradedProduct (avoidanceClass τ) := by
  classical
  by_cases hτ : SumIndecomposable τ
  · exact directAvoidanceProduct τ hτ
  · exact skewAvoidanceProduct τ
      ((sumIndecomposable_or_skewIndecomposable τ).resolve_left hτ)

/-- Concrete supermultiplicativity: there is no constructor hypothesis. -/
theorem avoiderCount_supermultiplicative (τ : Perm k) :
    Supermultiplicative (avoiderCount τ) :=
  (avoidanceProduct τ).counts_supermultiplicative

end StanleyWilf
