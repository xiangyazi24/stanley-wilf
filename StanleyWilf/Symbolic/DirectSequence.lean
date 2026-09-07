import StanleyWilf.Permutation.Split
import StanleyWilf.Permutation.Closure
import StanleyWilf.Symbolic.FirstComponent

/-!
# Concrete symbolic sequence specification for sum-indecomposable avoidance

The first-component constructor is an actual direct sum. Injectivity follows
from the unique first positive boundary, not from an assumed count identity.
Surjectivity recovers the two actual subpermutations at that boundary.

A nonempty forbidden pattern is necessary: the empty pattern has no empty
avoider, whereas every SEQ class contains the empty sequence.
-/

namespace StanleyWilf

open AnalyticCombinatorics.Ch1

variable {k : ℕ}

/-- Positive-size, sum-indecomposable avoiders: precisely the intended atoms. -/
noncomputable def sumAtomClass (τ : Perm k) : CombClass where
  Obj n := {σ : Perm n // 0 < n ∧ Avoids τ σ ∧ SumIndecomposable σ}
  finObj _ := by classical exact inferInstance

theorem sumAtomClass_zero (τ : Perm k) : (sumAtomClass τ).counts 0 = 0 := by
  classical
  letI : IsEmpty ((sumAtomClass τ).Obj 0) := ⟨fun a => Nat.lt_irrefl 0 a.property.1⟩
  exact Fintype.card_eq_zero

theorem avoidanceClass_zero (τ : Perm k) (hk : 0 < k) :
    (avoidanceClass τ).counts 0 = 1 := by
  classical
  letI : Unique (Avoider τ 0) :=
    { default := ⟨Equiv.refl _, avoids_of_size_lt τ (Equiv.refl _) hk⟩
      uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
  exact Fintype.card_unique

/-- Join a first component of size `j+1` and the remaining `n-j` positions. -/
def joinFirst (n : ℕ) (j : Fin (n + 1))
    (σ : Perm (j.val + 1)) (π : Perm (n - j.val)) : Perm (n + 1) :=
  castPerm (by have := j.isLt; omega) (directSum σ π)

theorem firstSumBoundary_joinFirst (n : ℕ) (j : Fin (n + 1))
    (σ : Perm (j.val + 1)) (π : Perm (n - j.val))
    (hσ : SumIndecomposable σ) :
    firstSumBoundary (joinFirst n j σ π) (Nat.succ_pos n) = j.val + 1 := by
  apply firstSumBoundary_eq_of_first
  exact (first_boundary_directSum σ π (Nat.succ_pos _) hσ).cast _

abbrev DirectFirstFactors (τ : Perm k) (n : ℕ) :=
  Σ j : Fin (n + 1), (sumAtomClass τ).Obj (j.val + 1) ×
    (avoidanceClass τ).Obj (n - j.val)

/-- The concrete first-component constructor on avoidance subtypes. -/
noncomputable def directFirstJoin (τ : Perm k) (hτ : SumIndecomposable τ) (n : ℕ)
    (p : DirectFirstFactors τ n) : (avoidanceClass τ).Obj (n + 1) :=
  ⟨joinFirst n p.1 p.2.1.val p.2.2.val, by
    apply (avoids_castPerm τ _ _).mpr
    exact avoids_directSum hτ p.2.1.property.2.1 p.2.2.property⟩

/-- Unlike arbitrary direct-sum pairs, indecomposable-first pairs have a unique cut. -/
theorem directFirstJoin_injective (τ : Perm k) (hτ : SumIndecomposable τ) (n : ℕ) :
    Function.Injective (directFirstJoin τ hτ n) := by
  rintro ⟨i, a, b⟩ ⟨j, a', b'⟩ he
  have hv := congrArg Subtype.val he
  change joinFirst n i a.val b.val = joinFirst n j a'.val b'.val at hv
  have hs := congrArg (fun σ : Perm (n + 1) =>
    firstSumBoundary σ (Nat.succ_pos n)) hv
  rw [firstSumBoundary_joinFirst n i a.val b.val a.property.2.2,
      firstSumBoundary_joinFirst n j a'.val b'.val a'.property.2.2] at hs
  have hij : i = j := Fin.ext (by omega)
  subst j
  have hp : directSum a.val b.val = directSum a'.val b'.val :=
    castPerm_injective _ hv
  have hp' := directSum_injective (i.val + 1) (n - i.val) hp
  have ha : a = a' := Subtype.ext (congrArg Prod.fst hp')
  have hb : b = b' := Subtype.ext (congrArg Prod.snd hp')
  subst a'
  subst b'
  rfl

/-- Every nonempty avoider has an actual indecomposable first factor and an
actual avoiding suffix. No surjectivity assumption is passed in. -/
theorem directFirstJoin_surjective (τ : Perm k) (hτ : SumIndecomposable τ) (n : ℕ) :
    Function.Surjective (directFirstJoin τ hτ n) := by
  intro p
  let c := firstSumBoundary p.val (Nat.succ_pos n)
  have hc : IsFirstSumBoundary p.val c := firstSumBoundary_spec p.val (Nat.succ_pos n)
  let j : Fin (n + 1) := ⟨c - 1, by have := hc.1; have := hc.2.1.1; omega⟩
  have hj : j.val + 1 = c := by change c - 1 + 1 = c; have := hc.1; omega
  have hf : IsFirstSumBoundary p.val (j.val + 1) := by simpa only [hj] using hc
  let a : (sumAtomClass τ).Obj (j.val + 1) :=
    ⟨prefixPerm p.val hf.2.1, Nat.succ_pos _,
      avoids_prefixPerm hf.2.1 p.property, prefixPerm_indecomposable_of_first p.val hf⟩
  have hrest : (n + 1) - (j.val + 1) = n - j.val := by omega
  let b : (avoidanceClass τ).Obj (n - j.val) :=
    ⟨castPerm hrest (suffixPerm p.val hf.2.1),
      (avoids_castPerm τ hrest _).mpr (avoids_suffixPerm hf.2.1 p.property)⟩
  refine ⟨⟨j, a, b⟩, ?_⟩
  apply Subtype.ext
  change castPerm _ (directSum (prefixPerm p.val hf.2.1)
    (castPerm hrest (suffixPerm p.val hf.2.1))) = p.val
  rw [← castPerm_directSum_right, castPerm_trans]
  exact reconstruct_prefix_suffix p.val hf.2.1

/-- The genuine object-level first-component bijection. -/
noncomputable def directFirstEquiv (τ : Perm k) (hτ : SumIndecomposable τ) (n : ℕ) :
    (avoidanceClass τ).Obj (n + 1) ≃ DirectFirstFactors τ n :=
  (Equiv.ofBijective (directFirstJoin τ hτ n)
    ⟨directFirstJoin_injective τ hτ n, directFirstJoin_surjective τ hτ n⟩).symm

/-- `Av(τ) = ε + I × Av(τ)` for the actual indecomposable avoiding class. -/
noncomputable def directFirstComponentSpecification (τ : Perm k) (hk : 0 < k)
    (hτ : SumIndecomposable τ) :
    FirstComponentSpecification (avoidanceClass τ) (sumAtomClass τ) where
  noEmptyAtom := sumAtomClass_zero τ
  emptyCount := avoidanceClass_zero τ hk
  split := directFirstEquiv τ hτ

/-- The size-wise SEQ equivalence is derived, not an additional hypothesis.
This wrapper chooses a finite-cardinality equivalence; `directFirstEquiv` is
the structural, canonical-first-factor interface. -/
noncomputable def directSequenceSpecification (τ : Perm k) (hk : 0 < k)
    (hτ : SumIndecomposable τ) :
    SequenceSpecification (avoidanceClass τ) (sumAtomClass τ) :=
  (directFirstComponentSpecification τ hk hτ).toSequenceSpecification

theorem avoidance_ogf_direct (τ : Perm k) (hk : 0 < k) (hτ : SumIndecomposable τ) :
    (avoidanceClass τ).ogf * (1 - (sumAtomClass τ).ogf) = 1 :=
  (directSequenceSpecification τ hk hτ).ogf_mul_one_sub

end StanleyWilf
