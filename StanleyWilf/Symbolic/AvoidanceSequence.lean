import StanleyWilf.Symbolic.DirectSequence
import StanleyWilf.Permutation.Complement

/-!
# The concrete SEQ specification for every nonempty forbidden pattern

The skew case is transported through value complement at the object level.
Its atoms are actual skew-indecomposable avoiders, not a relabelled arbitrary
counting sequence. No growth bound is needed for these formal identities.
-/

namespace StanleyWilf

open AnalyticCombinatorics.Ch1

variable {k : ℕ}

noncomputable def skewAtomClass (τ : Perm k) : CombClass where
  Obj n := {σ : Perm n // 0 < n ∧ Avoids τ σ ∧ SkewIndecomposable σ}
  finObj _ := by classical exact inferInstance

theorem skewAtomClass_zero (τ : Perm k) : (skewAtomClass τ).counts 0 = 0 := by
  classical
  letI : IsEmpty ((skewAtomClass τ).Obj 0) := ⟨fun a => Nat.lt_irrefl 0 a.property.1⟩
  exact Fintype.card_eq_zero

noncomputable def complementAvoiderEquiv (τ : Perm k) (n : ℕ) :
    (avoidanceClass τ).Obj n ≃ (avoidanceClass (complement τ)).Obj n where
  toFun p := ⟨complement p.val, (avoids_complement_iff τ p.val).mpr p.property⟩
  invFun p := ⟨complement p.val, by
    have hp := (avoids_complement_iff (complement τ) p.val).mpr p.property
    simpa only [complement_twice] using hp⟩
  left_inv p := Subtype.ext (complement_twice p.val)
  right_inv p := Subtype.ext (complement_twice p.val)

/-- The reflected atoms are exactly the sum-indecomposable reflected avoiders. -/
noncomputable def complementAtomEquiv (τ : Perm k) (n : ℕ) :
    (skewAtomClass τ).Obj n ≃ (sumAtomClass (complement τ)).Obj n where
  toFun p := ⟨complement p.val, p.property.1,
    (avoids_complement_iff τ p.val).mpr p.property.2.1,
    (sumIndecomposable_complement_iff p.val).mpr p.property.2.2⟩
  invFun p := ⟨complement p.val, p.property.1, by
    have hp := (avoids_complement_iff (complement τ) p.val).mpr p.property.2.1
    simpa only [complement_twice] using hp,
    (skewIndecomposable_complement_iff p.val).mpr p.property.2.2⟩
  left_inv p := Subtype.ext (complement_twice p.val)
  right_inv p := Subtype.ext (complement_twice p.val)

/-- Complement, perform the genuine direct first-factor split, and reflect
both output factors back. -/
noncomputable def skewFirstEquiv (τ : Perm k) (hτ : SkewIndecomposable τ) (n : ℕ) :
    (avoidanceClass τ).Obj (n + 1) ≃
      (Σ j : Fin (n + 1), (skewAtomClass τ).Obj (j.val + 1) ×
        (avoidanceClass τ).Obj (n - j.val)) :=
  (complementAvoiderEquiv τ (n + 1)).trans
    ((directFirstEquiv (complement τ)
      ((sumIndecomposable_complement_iff τ).mpr hτ) n).trans
        (Equiv.sigmaCongrRight fun j =>
          Equiv.prodCongr (complementAtomEquiv τ (j.val + 1)).symm
            (complementAvoiderEquiv τ (n - j.val)).symm))

noncomputable def skewFirstComponentSpecification (τ : Perm k) (hk : 0 < k)
    (hτ : SkewIndecomposable τ) :
    FirstComponentSpecification (avoidanceClass τ) (skewAtomClass τ) where
  noEmptyAtom := skewAtomClass_zero τ
  emptyCount := avoidanceClass_zero τ hk
  split := skewFirstEquiv τ hτ

noncomputable def skewSequenceSpecification (τ : Perm k) (hk : 0 < k)
    (hτ : SkewIndecomposable τ) :
    SequenceSpecification (avoidanceClass τ) (skewAtomClass τ) :=
  (skewFirstComponentSpecification τ hk hτ).toSequenceSpecification

/-- Select the operation once, as a function of the forbidden pattern only. -/
noncomputable def indecomposableAtomClass (τ : Perm k) : CombClass := by
  classical
  exact if SumIndecomposable τ then sumAtomClass τ else skewAtomClass τ

/-- The chosen operation has an actual first-component bijection. -/
noncomputable def avoidanceFirstComponentSpecification (τ : Perm k) (hk : 0 < k) :
    FirstComponentSpecification (avoidanceClass τ) (indecomposableAtomClass τ) := by
  classical
  by_cases hτ : SumIndecomposable τ
  · simpa only [indecomposableAtomClass, if_pos hτ] using
      directFirstComponentSpecification τ hk hτ
  · have hs := (sumIndecomposable_or_skewIndecomposable τ).resolve_left hτ
    simpa only [indecomposableAtomClass, if_neg hτ] using
      skewFirstComponentSpecification τ hk hs

/-- The concrete symbolic specification has no unfilled decomposition input.
The final size-wise equivalences are cardinality transports from the proved
first-component bijections; no canonical full-factor-list map is claimed. -/
noncomputable def avoidanceSequenceSpecification (τ : Perm k) (hk : 0 < k) :
    SequenceSpecification (avoidanceClass τ) (indecomposableAtomClass τ) :=
  (avoidanceFirstComponentSpecification τ hk).toSequenceSpecification

/-- An alternative to the earlier binary-product proof, derived from the
actual symbolic first-component recurrence. -/
theorem avoiderCount_supermultiplicative_symbolic (τ : Perm k) (hk : 0 < k) :
    Supermultiplicative (avoiderCount τ) :=
  (avoidanceFirstComponentSpecification τ hk).counts_supermultiplicative

/-- The formal symbolic-method identity for the actual avoidance class. -/
theorem avoidance_ogf_mul_one_sub (τ : Perm k) (hk : 0 < k) :
    (avoidanceClass τ).ogf * (1 - (indecomposableAtomClass τ).ogf) = 1 :=
  (avoidanceSequenceSpecification τ hk).ogf_mul_one_sub

/-- Equality at every coefficient, before any analytic limit is taken. -/
theorem avoidance_counts_seq (τ : Perm k) (hk : 0 < k) (n : ℕ) :
    avoiderCount τ n = (indecomposableAtomClass τ).seq.counts n :=
  (avoidanceSequenceSpecification τ hk).counts_eq n

end StanleyWilf
