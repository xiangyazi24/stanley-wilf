import StanleyWilf.Permutation.Basic

/-! # Empty and one-element forbidden patterns

These cases are treated before taking logarithms. The singleton pattern
has no avoider of positive size; the empty pattern has no avoider at all.
-/

namespace StanleyWilf

variable {k n : ℕ}

/-- The unique empty selection is an occurrence of the empty pattern. -/
def Occurrence.empty (τ : Perm 0) (σ : Perm n) : Occurrence τ σ where
  position := OrderEmbedding.ofIsEmpty
  pattern i _ := Fin.elim0 i

/-- Select the first position to witness any one-element pattern. -/
def Occurrence.singleton (τ : Perm 1) (σ : Perm n) (hn : 0 < n) : Occurrence τ σ where
  position := OrderEmbedding.ofStrictMono (fun _ : Fin 1 => (⟨0, hn⟩ : Fin n)) (by
    intro i j hij
    have heq : i = j := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hij) heq))
  pattern i j := by
    have heq : i = j := Subsingleton.elim _ _
    subst j
    simp

theorem contains_of_length_le_one (τ : Perm k) (σ : Perm n)
    (hk : k ≤ 1) (hn : 0 < n) : Contains τ σ := by
  cases k with
  | zero => exact ⟨Occurrence.empty τ σ⟩
  | succ k =>
    have hk0 : k = 0 := by omega
    subst k
    exact ⟨Occurrence.singleton τ σ hn⟩

/-- No logarithm-of-zero convention is used in this counting statement. -/
theorem avoiderCount_eq_zero_of_length_le_one (τ : Perm k) (hk : k ≤ 1)
    {n : ℕ} (hn : 0 < n) : avoiderCount τ n = 0 := by
  classical
  change Fintype.card (Avoider τ n) = 0
  letI : IsEmpty (Avoider τ n) :=
    ⟨fun p => p.property (contains_of_length_le_one τ p.val hk hn)⟩
  simp

end StanleyWilf
