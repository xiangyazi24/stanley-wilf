import StanleyWilf.Permutation.Basic

/-!
# Block permutations and fixed-size injectivity

The input positions always put the `m`-block before the `n`-block. The value
embedding determines whether the result is a direct or skew sum. Separating
that embedding makes the injectivity proof common to both operations.

The order formulas here are used by `Permutation/Closure.lean`.
-/

namespace StanleyWilf

variable {m n : ℕ}

/-- Join two permutations, using a supplied bijection to order their values. -/
def blockJoin (values : Fin m ⊕ Fin n ≃ Fin (m + n))
    (σ : Perm m) (π : Perm n) : Perm (m + n) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ π).trans values)

@[simp] theorem blockJoin_inl (values : Fin m ⊕ Fin n ≃ Fin (m + n))
    (σ : Perm m) (π : Perm n) (i : Fin m) :
    blockJoin values σ π (finSumFinEquiv (Sum.inl i)) = values (Sum.inl (σ i)) := by
  simp [blockJoin]

@[simp] theorem blockJoin_inr (values : Fin m ⊕ Fin n ≃ Fin (m + n))
    (σ : Perm m) (π : Perm n) (j : Fin n) :
    blockJoin values σ π (finSumFinEquiv (Sum.inr j)) = values (Sum.inr (π j)) := by
  simp [blockJoin]

/-- The sizes `m,n` are fixed: both blocks can be recovered from the result. -/
theorem blockJoin_injective (values : Fin m ⊕ Fin n ≃ Fin (m + n)) :
    Function.Injective (fun p : Perm m × Perm n => blockJoin values p.1 p.2) := by
  rintro ⟨σ, π⟩ ⟨σ', π'⟩ h
  change blockJoin values σ π = blockJoin values σ' π' at h
  have hσ : σ = σ' := by
    apply Equiv.ext
    intro i
    have hi := congrArg
      (fun p : Perm (m + n) => p (finSumFinEquiv (Sum.inl i))) h
    simp only [blockJoin_inl] at hi
    exact Sum.inl.inj (values.injective hi)
  have hπ : π = π' := by
    apply Equiv.ext
    intro j
    have hj := congrArg
      (fun p : Perm (m + n) => p (finSumFinEquiv (Sum.inr j))) h
    simp only [blockJoin_inr] at hj
    exact Sum.inr.inj (values.injective hj)
  exact Prod.ext hσ hπ

def directSum (σ : Perm m) (π : Perm n) : Perm (m + n) :=
  blockJoin finSumFinEquiv σ π

/-- Swap the value blocks, not the position blocks. -/
def skewValues (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  (Equiv.sumComm (Fin m) (Fin n)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm n m)))

def skewSum (σ : Perm m) (π : Perm n) : Perm (m + n) :=
  blockJoin (skewValues m n) σ π

theorem directSum_injective (m n : ℕ) :
    Function.Injective (fun p : Perm m × Perm n => directSum p.1 p.2) :=
  blockJoin_injective finSumFinEquiv

theorem skewSum_injective (m n : ℕ) :
    Function.Injective (fun p : Perm m × Perm n => skewSum p.1 p.2) :=
  blockJoin_injective (skewValues m n)

/-! ### Numeric formulas on each position block -/

@[simp] theorem directSum_castAdd_val (σ : Perm m) (π : Perm n) (i : Fin m) :
    (directSum σ π (Fin.castAdd n i)).val = (σ i).val := by
  simp [directSum, blockJoin]

@[simp] theorem directSum_natAdd_val (σ : Perm m) (π : Perm n) (j : Fin n) :
    (directSum σ π (Fin.natAdd m j)).val = m + (π j).val := by
  simp [directSum, blockJoin]

@[simp] theorem skewSum_castAdd_val (σ : Perm m) (π : Perm n) (i : Fin m) :
    (skewSum σ π (Fin.castAdd n i)).val = n + (σ i).val := by
  simp [skewSum, blockJoin, skewValues, finCongr]

@[simp] theorem skewSum_natAdd_val (σ : Perm m) (π : Perm n) (j : Fin n) :
    (skewSum σ π (Fin.natAdd m j)).val = (π j).val := by
  simp [skewSum, blockJoin, skewValues, finCongr]

/-- Within each block the direct sum preserves relative order. -/
theorem directSum_left_lt_iff (σ : Perm m) (π : Perm n) (i j : Fin m) :
    directSum σ π (Fin.castAdd n i) < directSum σ π (Fin.castAdd n j) ↔ σ i < σ j := by
  change (directSum σ π (Fin.castAdd n i)).val <
    (directSum σ π (Fin.castAdd n j)).val ↔ (σ i).val < (σ j).val
  rw [directSum_castAdd_val, directSum_castAdd_val]

theorem directSum_right_lt_iff (σ : Perm m) (π : Perm n) (i j : Fin n) :
    directSum σ π (Fin.natAdd m i) < directSum σ π (Fin.natAdd m j) ↔ π i < π j := by
  change (directSum σ π (Fin.natAdd m i)).val <
    (directSum σ π (Fin.natAdd m j)).val ↔ (π i).val < (π j).val
  rw [directSum_natAdd_val, directSum_natAdd_val]
  omega

/-- Swapping value blocks does not reverse relative order inside a block. -/
theorem skewSum_left_lt_iff (σ : Perm m) (π : Perm n) (i j : Fin m) :
    skewSum σ π (Fin.castAdd n i) < skewSum σ π (Fin.castAdd n j) ↔ σ i < σ j := by
  change (skewSum σ π (Fin.castAdd n i)).val <
    (skewSum σ π (Fin.castAdd n j)).val ↔ (σ i).val < (σ j).val
  rw [skewSum_castAdd_val, skewSum_castAdd_val]
  omega

theorem skewSum_right_lt_iff (σ : Perm m) (π : Perm n) (i j : Fin n) :
    skewSum σ π (Fin.natAdd m i) < skewSum σ π (Fin.natAdd m j) ↔ π i < π j := by
  change (skewSum σ π (Fin.natAdd m i)).val <
    (skewSum σ π (Fin.natAdd m j)).val ↔ (π i).val < (π j).val
  rw [skewSum_natAdd_val, skewSum_natAdd_val]

/-- Values in the left direct-sum block precede every value in the right block. -/
theorem directSum_cross (σ : Perm m) (π : Perm n) {i j : Fin (m + n)}
    (hi : i.val < m) (hj : m ≤ j.val) : directSum σ π i < directSum σ π j := by
  let il : Fin m := ⟨i.val, hi⟩
  let jr : Fin n := ⟨j.val - m, by have h := j.isLt; omega⟩
  have hei : Fin.castAdd n il = i := by apply Fin.ext; rfl
  have hej : Fin.natAdd m jr = j := by
    apply Fin.ext
    change m + (j.val - m) = j.val
    omega
  rw [← hei, ← hej]
  change (directSum σ π (Fin.castAdd n il)).val <
    (directSum σ π (Fin.natAdd m jr)).val
  rw [directSum_castAdd_val, directSum_natAdd_val]
  have h := (σ il).isLt
  omega

/-- Values in the right skew-sum block precede every value in the left block. -/
theorem skewSum_cross (σ : Perm m) (π : Perm n) {i j : Fin (m + n)}
    (hi : i.val < m) (hj : m ≤ j.val) : skewSum σ π j < skewSum σ π i := by
  let il : Fin m := ⟨i.val, hi⟩
  let jr : Fin n := ⟨j.val - m, by have h := j.isLt; omega⟩
  have hei : Fin.castAdd n il = i := by apply Fin.ext; rfl
  have hej : Fin.natAdd m jr = j := by
    apply Fin.ext
    change m + (j.val - m) = j.val
    omega
  rw [← hei, ← hej]
  change (skewSum σ π (Fin.natAdd m jr)).val <
    (skewSum σ π (Fin.castAdd n il)).val
  rw [skewSum_natAdd_val, skewSum_castAdd_val]
  have h := (π jr).isLt
  omega

end StanleyWilf
