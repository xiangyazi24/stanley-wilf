import StanleyWilf.Permutation.Boundary

/-!
# Recovering the two actual permutations at an invariant prefix

Both pieces are constructed as bijections of finite sets, not as unverified
standardizations. The reconstruction and pattern-embedding lemmas connect
canonical boundaries to the existing avoidance definitions.
-/

namespace StanleyWilf

variable {n c d : ℕ}

/-- Restrict the values of a boundary-invariant permutation to its prefix. -/
def prefixMap (σ : Perm n) (h : SumBoundary σ c) (i : Fin c) : Fin c :=
  ⟨(σ (Fin.castLE h.1 i)).val, h.2 _ i.isLt⟩

theorem prefixMap_injective (σ : Perm n) (h : SumBoundary σ c) :
    Function.Injective (prefixMap σ h) := by
  intro i j hij
  have hval : (σ (Fin.castLE h.1 i)).val =
      (σ (Fin.castLE h.1 j)).val := by
    change (prefixMap σ h i).val = (prefixMap σ h j).val
    exact congrArg Fin.val hij
  have he : σ (Fin.castLE h.1 i) = σ (Fin.castLE h.1 j) :=
    Fin.ext hval
  apply Fin.ext
  have hval' : (Fin.castLE h.1 i).val = (Fin.castLE h.1 j).val :=
    congrArg Fin.val (σ.injective he)
  simpa using hval'

noncomputable def prefixPerm (σ : Perm n) (h : SumBoundary σ c) : Perm c :=
  Equiv.ofBijective (prefixMap σ h)
    ⟨prefixMap_injective σ h, Finite.surjective_of_injective (prefixMap_injective σ h)⟩

@[simp] theorem prefixPerm_val (σ : Perm n) (h : SumBoundary σ c) (i : Fin c) :
    (prefixPerm σ h i).val = (σ (Fin.castLE h.1 i)).val := rfl

/-- The increasing position embedding for the suffix. -/
def suffixPosition (hcn : c ≤ n) (i : Fin (n - c)) : Fin n :=
  ⟨c + i.val, by have hi := i.isLt; omega⟩

@[simp] theorem suffixPosition_val (hcn : c ≤ n) (i : Fin (n - c)) :
    (suffixPosition hcn i).val = c + i.val := rfl

def suffixMap (σ : Perm n) (h : SumBoundary σ c) (i : Fin (n - c)) : Fin (n - c) :=
  ⟨(σ (suffixPosition h.1 i)).val - c, by
    have hlt := (σ (suffixPosition h.1 i)).isLt
    have hge := h.value_ge (i := suffixPosition h.1 i) (by
      change c ≤ c + i.val
      omega)
    omega⟩

theorem suffixMap_injective (σ : Perm n) (h : SumBoundary σ c) :
    Function.Injective (suffixMap σ h) := by
  intro i j hij
  have he := congrArg Fin.val hij
  change (σ (suffixPosition h.1 i)).val - c =
    (σ (suffixPosition h.1 j)).val - c at he
  have hi := h.value_ge (i := suffixPosition h.1 i) (by
    change c ≤ c + i.val
    omega)
  have hj := h.value_ge (i := suffixPosition h.1 j) (by
    change c ≤ c + j.val
    omega)
  have he' : σ (suffixPosition h.1 i) = σ (suffixPosition h.1 j) :=
    Fin.ext (by omega)
  have hp := congrArg Fin.val (σ.injective he')
  change c + i.val = c + j.val at hp
  exact Fin.ext (by omega)

noncomputable def suffixPerm (σ : Perm n) (h : SumBoundary σ c) : Perm (n - c) :=
  Equiv.ofBijective (suffixMap σ h)
    ⟨suffixMap_injective σ h, Finite.surjective_of_injective (suffixMap_injective σ h)⟩

@[simp] theorem suffixPerm_val (σ : Perm n) (h : SumBoundary σ c) (i : Fin (n - c)) :
    (suffixPerm σ h i).val = (σ (suffixPosition h.1 i)).val - c := rfl

/-- The prefix is a pattern of the original permutation, with its exact order. -/
def prefixOccurrence (σ : Perm n) (h : SumBoundary σ c) :
    Occurrence (prefixPerm σ h) σ where
  position := OrderEmbedding.ofStrictMono (Fin.castLE h.1) (by
    intro i j hij
    exact hij)
  pattern i j := Iff.rfl

/-- Removing the common suffix offset preserves every comparison. -/
def suffixOccurrence (σ : Perm n) (h : SumBoundary σ c) :
    Occurrence (suffixPerm σ h) σ where
  position := OrderEmbedding.ofStrictMono (suffixPosition h.1) (by
    intro i j hij
    change c + i.val < c + j.val
    change i.val < j.val at hij
    omega)
  pattern i j := by
    change (σ (suffixPosition h.1 i)).val - c <
      (σ (suffixPosition h.1 j)).val - c ↔
      (σ (suffixPosition h.1 i)).val < (σ (suffixPosition h.1 j)).val
    have hi := h.value_ge (i := suffixPosition h.1 i) (by
      change c ≤ c + i.val
      omega)
    have hj := h.value_ge (i := suffixPosition h.1 j) (by
      change c ≤ c + j.val
      omega)
    omega

/-- Exact recovery, including either empty block. -/
theorem reconstruct_prefix_suffix (σ : Perm n) (h : SumBoundary σ c) :
    castPerm (show c + (n - c) = n by have := h.1; omega)
      (directSum (prefixPerm σ h) (suffixPerm σ h)) = σ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [castPerm_apply_val]
  by_cases hi : i.val < c
  · let j : Fin c := ⟨i.val, hi⟩
    have he : Fin.castAdd (n - c) j =
        Fin.cast (show n = c + (n - c) by have := h.1; omega) i := Fin.ext rfl
    rw [← he, directSum_castAdd_val, prefixPerm_val]
    have he' : Fin.castLE h.1 j = i := Fin.ext rfl
    rw [he']
  · let j : Fin (n - c) := ⟨i.val - c, by have := i.isLt; omega⟩
    have he : Fin.natAdd c j =
        Fin.cast (show n = c + (n - c) by have := h.1; omega) i := by
      apply Fin.ext
      change c + (i.val - c) = i.val
      omega
    rw [← he, directSum_natAdd_val, suffixPerm_val]
    have he' : suffixPosition h.1 j = i := by
      apply Fin.ext
      change c + (i.val - c) = i.val
      omega
    rw [he']
    have hv := h.value_ge (Nat.le_of_not_gt hi)
    omega

/-- Any smaller boundary of the recovered prefix lifts to the whole permutation. -/
theorem prefixPerm_boundary_iff (σ : Perm n) (h : SumBoundary σ c) (hd : d ≤ c) :
    SumBoundary (prefixPerm σ h) d ↔ SumBoundary σ d := by
  constructor
  · intro hb
    refine ⟨by have := h.1; omega, ?_⟩
    intro i hi
    let j : Fin c := ⟨i.val, by omega⟩
    have hv := hb.2 j hi
    rw [prefixPerm_val] at hv
    have he : Fin.castLE h.1 j = i := Fin.ext rfl
    simpa only [he] using hv
  · intro hb
    refine ⟨hd, ?_⟩
    intro i hi
    exact hb.2 (Fin.castLE h.1 i) hi

/-- Minimality proves that the actual first factor is indecomposable. -/
theorem prefixPerm_indecomposable_of_first (σ : Perm n)
    (h : IsFirstSumBoundary σ c) : SumIndecomposable (prefixPerm σ h.2.1) := by
  rintro ⟨d, hd⟩
  have hb := (prefixPerm_boundary_iff σ h.2.1 (Nat.le_of_lt hd.2.1)).mp hd.to_boundary
  exact h.2.2 d hd.1 hd.2.1 hb

/-- Hereditary avoidance now applies to the actual recovered pieces. -/
theorem avoids_prefixPerm {k : ℕ} {τ : Perm k} {σ : Perm n}
    (h : SumBoundary σ c) (ha : Avoids τ σ) : Avoids τ (prefixPerm σ h) :=
  avoids_of_contains ⟨prefixOccurrence σ h⟩ ha

theorem avoids_suffixPerm {k : ℕ} {τ : Perm k} {σ : Perm n}
    (h : SumBoundary σ c) (ha : Avoids τ σ) : Avoids τ (suffixPerm σ h) :=
  avoids_of_contains ⟨suffixOccurrence σ h⟩ ha

end StanleyWilf
