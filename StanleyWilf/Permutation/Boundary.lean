import StanleyWilf.Permutation.Cuts
import StanleyWilf.Permutation.BlockSum

/-!
# Prefix-invariant boundaries and the canonical first component

`SumBoundary σ c` says that the first `c` positions are invariant under `σ`.
Unlike `IsSumCut`, it includes both endpoints. The equivalence with a genuine
nontrivial cut uses finiteness and bijectivity; it is not definitional.

The first positive boundary exists for every nonempty permutation. It will
supply the unique first indecomposable component of the symbolic sequence.
-/

namespace StanleyWilf

variable {n m c d : ℕ}

/-- Transport a permutation across an equality of its size. -/
def castPerm (h : m = n) (σ : Perm m) : Perm n := h ▸ σ

@[simp] theorem castPerm_rfl (σ : Perm n) : castPerm rfl σ = σ := rfl

@[simp] theorem castPerm_apply_val (h : m = n) (σ : Perm m) (i : Fin n) :
    (castPerm h σ i).val = (σ (Fin.cast h.symm i)).val := by
  subst n
  rfl

@[simp] theorem castPerm_trans {a b e : ℕ} (h : a = b) (g : b = e) (σ : Perm a) :
    castPerm g (castPerm h σ) = castPerm (h.trans g) σ := by
  subst b
  subst e
  rfl

theorem castPerm_directSum_right {a b e : ℕ} (h : b = e)
    (σ : Perm a) (π : Perm b) :
    castPerm (congrArg (fun x => a + x) h) (directSum σ π) =
      directSum σ (castPerm h π) := by
  subst e
  rfl

theorem castPerm_injective (h : m = n) : Function.Injective (castPerm h) := by
  subst n
  exact fun _ _ hσ => hσ

@[simp] theorem avoids_castPerm {k : ℕ} (τ : Perm k) (h : m = n) (σ : Perm m) :
    Avoids τ (castPerm h σ) ↔ Avoids τ σ := by
  subst n
  rfl

/-- A boundary, including zero and the full length. -/
def SumBoundary (σ : Perm n) (c : ℕ) : Prop :=
  c ≤ n ∧ ∀ i : Fin n, i.val < c → (σ i).val < c

/-- A finite permutation preserving a subset also reflects membership in it. -/
private theorem mem_iff_of_forward_invariant {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (P : α → Prop) (hP : ∀ x, P x → P (σ x)) :
    ∀ x, P (σ x) ↔ P x := by
  classical
  let f : {x // P x} → {x // P x} := fun x => ⟨σ x.val, hP x.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (σ.injective (congrArg Subtype.val h))
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨σ x, hx⟩
    have hyx : y.val = x := σ.injective (congrArg Subtype.val hy)
    simpa only [hyx] using y.property
  · exact hP x

theorem SumBoundary.value_lt_iff {σ : Perm n} (h : SumBoundary σ c) (i : Fin n) :
    (σ i).val < c ↔ i.val < c :=
  mem_iff_of_forward_invariant σ (fun x : Fin n => x.val < c) h.2 i

theorem SumBoundary.value_ge {σ : Perm n} (h : SumBoundary σ c)
    {i : Fin n} (hi : c ≤ i.val) : c ≤ (σ i).val := by
  have hiff := h.value_lt_iff i
  omega

@[simp] theorem sumBoundary_zero (σ : Perm n) : SumBoundary σ 0 := by
  exact ⟨Nat.zero_le _, fun _ h => (Nat.not_lt_zero _ h).elim⟩

@[simp] theorem sumBoundary_full (σ : Perm n) : SumBoundary σ n :=
  ⟨le_rfl, fun i _ => (σ i).isLt⟩

@[simp] theorem sumBoundary_castPerm (h : m = n) (σ : Perm m) (c : ℕ) :
    SumBoundary (castPerm h σ) c ↔ SumBoundary σ c := by
  subst n
  rfl

/-- Separating all left and right values forces the left values to be exactly
`0,...,c-1`. A finite pigeonhole argument is essential in this direction. -/
theorem IsSumCut.to_boundary {σ : Perm n} (h : IsSumCut σ c) : SumBoundary σ c := by
  refine ⟨Nat.le_of_lt h.2.1, ?_⟩
  intro i hi
  by_contra hbad
  have hc : c ≤ n := Nat.le_of_lt h.2.1
  have hpre : ∀ v : Fin c, (σ.symm (Fin.castLE hc v)).val < c := by
    intro v
    by_contra hv
    have hsep := h.2.2 i (σ.symm (Fin.castLE hc v)) hi (Nat.le_of_not_gt hv)
    simp only [Equiv.apply_symm_apply] at hsep
    change (σ i).val < v.val at hsep
    have hvlt := v.isLt
    omega
  let f : Fin c → Fin c := fun v => ⟨(σ.symm (Fin.castLE hc v)).val, hpre v⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have hval : (σ.symm (Fin.castLE hc v)).val =
        (σ.symm (Fin.castLE hc w)).val := by
      change (f v).val = (f w).val
      exact congrArg Fin.val hvw
    have he : σ.symm (Fin.castLE hc v) = σ.symm (Fin.castLE hc w) :=
      Fin.ext hval
    have hvw' := σ.symm.injective he
    apply Fin.ext
    have hval' : (Fin.castLE hc v).val = (Fin.castLE hc w).val :=
      congrArg Fin.val hvw'
    simpa using hval'
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hf ⟨i.val, hi⟩
  have hval : (σ.symm (Fin.castLE hc v)).val = i.val := by
    change (f v).val = i.val
    exact congrArg Fin.val hv
  have he : σ.symm (Fin.castLE hc v) = i := Fin.ext hval
  have he' : Fin.castLE hc v = σ i := by
    simpa only [Equiv.apply_symm_apply] using congrArg σ he
  have hgood : (σ i).val < c := by rw [← he']; exact v.isLt
  exact hbad hgood

theorem SumBoundary.to_cut {σ : Perm n} (h : SumBoundary σ c)
    (hc : 0 < c) (hcn : c < n) : IsSumCut σ c := by
  refine ⟨hc, hcn, ?_⟩
  intro i j hi hj
  have hil := h.2 i hi
  have hjr := h.value_ge hj
  change (σ i).val < (σ j).val
  omega

theorem isSumCut_iff_boundary (σ : Perm n) (c : ℕ) :
    IsSumCut σ c ↔ 0 < c ∧ c < n ∧ SumBoundary σ c := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.to_boundary⟩
  · rintro ⟨hc, hcn, h⟩
    exact h.to_cut hc hcn

/-- Every direct sum has its prescribed boundary. -/
theorem directSum_boundary (σ : Perm m) (π : Perm n) :
    SumBoundary (directSum σ π) m := by
  refine ⟨by omega, ?_⟩
  intro i hi
  let j : Fin m := ⟨i.val, hi⟩
  have he : Fin.castAdd n j = i := Fin.ext rfl
  rw [← he, directSum_castAdd_val]
  exact (σ j).isLt

/-- A boundary inside the first block is a boundary of that block itself. -/
theorem directSum_boundary_left_iff (σ : Perm m) (π : Perm n) (hd : d ≤ m) :
    SumBoundary (directSum σ π) d ↔ SumBoundary σ d := by
  constructor
  · intro h
    refine ⟨hd, ?_⟩
    intro i hi
    have hv := h.2 (Fin.castAdd n i) hi
    simpa only [directSum_castAdd_val] using hv
  · intro h
    refine ⟨by omega, ?_⟩
    intro i hi
    let j : Fin m := ⟨i.val, by omega⟩
    have he : Fin.castAdd n j = i := Fin.ext rfl
    rw [← he, directSum_castAdd_val]
    exact h.2 j hi

/-- The minimality property of a first positive boundary. -/
def IsFirstSumBoundary (σ : Perm n) (c : ℕ) : Prop :=
  0 < c ∧ SumBoundary σ c ∧ ∀ d, 0 < d → d < c → ¬ SumBoundary σ d

theorem IsFirstSumBoundary.cast {σ : Perm m} (h : m = n)
    (hb : IsFirstSumBoundary σ c) : IsFirstSumBoundary (castPerm h σ) c := by
  subst n
  exact hb

noncomputable def firstSumBoundary (σ : Perm n) (hn : 0 < n) : ℕ := by
  classical
  exact Nat.find (show ∃ c, 0 < c ∧ SumBoundary σ c from
    ⟨n, hn, sumBoundary_full σ⟩)

theorem firstSumBoundary_spec (σ : Perm n) (hn : 0 < n) :
    IsFirstSumBoundary σ (firstSumBoundary σ hn) := by
  classical
  let hex : ∃ c, 0 < c ∧ SumBoundary σ c := ⟨n, hn, sumBoundary_full σ⟩
  change 0 < Nat.find hex ∧ SumBoundary σ (Nat.find hex) ∧ _
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro d hd hdc hbd
  exact Nat.find_min hex hdc ⟨hd, hbd⟩

theorem IsFirstSumBoundary.unique {σ : Perm n}
    (h : IsFirstSumBoundary σ c) (h' : IsFirstSumBoundary σ d) : c = d := by
  rcases lt_trichotomy c d with hlt | heq | hgt
  · exact False.elim (h'.2.2 c h.1 hlt h.2.1)
  · exact heq
  · exact False.elim (h.2.2 d h'.1 hgt h'.2.1)

theorem firstSumBoundary_eq_of_first {σ : Perm n} (hn : 0 < n)
    (h : IsFirstSumBoundary σ c) : firstSumBoundary σ hn = c :=
  (firstSumBoundary_spec σ hn).unique h

/-- An indecomposable first block is exactly the first positive boundary. -/
theorem first_boundary_directSum (σ : Perm m) (π : Perm n)
    (hm : 0 < m) (hσ : SumIndecomposable σ) :
    IsFirstSumBoundary (directSum σ π) m := by
  refine ⟨hm, directSum_boundary σ π, ?_⟩
  intro d hd hdm hbd
  have hleft := (directSum_boundary_left_iff σ π (Nat.le_of_lt hdm)).mp hbd
  exact hσ ⟨d, hleft.to_cut hd hdm⟩

@[simp] theorem firstSumBoundary_castPerm (h : m = n) (σ : Perm m)
    (hm : 0 < m) (hn : 0 < n) :
    firstSumBoundary (castPerm h σ) hn = firstSumBoundary σ hm := by
  subst n
  rfl

end StanleyWilf
