import StanleyWilf.Permutation.Basic

/-!
# Block permutations and fixed-size injectivity

The input positions always put the `m`-block before the `n`-block. The value
embedding determines whether the result is a direct or skew sum. Separating
that embedding makes the injectivity proof common to both operations.

This file does NOT yet prove avoidance closure under either operation.
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

end StanleyWilf
