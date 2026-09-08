import StanleyWilf.Permutation.Basic
import Mathlib.Data.Nat.Find

/-!
# Splitting an occurrence at a position-block boundary

The preimage of an initial interval under an order embedding is an initial
interval. If both sides are used, its endpoint is a genuine nontrivial cut.
All statements include empty domains and empty blocks.
-/

namespace StanleyWilf

variable {k m n : ℕ}

/-- Restrict a position embedding whose image lies entirely in the first block. -/
def restrictLeft (f : Fin k ↪o Fin (m + n))
    (hf : ∀ i, (f i).val < m) : Fin k ↪o Fin m :=
  OrderEmbedding.ofStrictMono (fun i => ⟨(f i).val, hf i⟩) (by
    intro i j hij
    change (f i).val < (f j).val
    exact f.strictMono hij)

@[simp] theorem castAdd_restrictLeft (f : Fin k ↪o Fin (m + n))
    (hf : ∀ i, (f i).val < m) (i : Fin k) :
    Fin.castAdd n (restrictLeft f hf i) = f i := by
  apply Fin.ext
  rfl

/-- Restrict to the second block, subtracting the position offset `m`. -/
def restrictRight (f : Fin k ↪o Fin (m + n))
    (hf : ∀ i, m ≤ (f i).val) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(f i).val - m, by
      have hlt := (f i).isLt
      have hge := hf i
      omega⟩)
    (by
      intro i j hij
      change (f i).val - m < (f j).val - m
      have hlt : (f i).val < (f j).val := f.strictMono hij
      have hge := hf i
      omega)

@[simp] theorem natAdd_restrictRight (f : Fin k ↪o Fin (m + n))
    (hf : ∀ i, m ≤ (f i).val) (i : Fin k) :
    Fin.natAdd m (restrictRight f hf i) = f i := by
  apply Fin.ext
  change m + ((f i).val - m) = (f i).val
  have hge := hf i
  omega

/-- An increasing selection lies in one block, or crosses at a nontrivial cut.
The equivalence records the entire preimage, not only a separating pair. -/
theorem positions_split {N : ℕ} (f : Fin k ↪o Fin N) (b : ℕ) :
    (∀ i, (f i).val < b) ∨
    (∀ i, b ≤ (f i).val) ∨
    ∃ c, 0 < c ∧ c < k ∧ ∀ i, (f i).val < b ↔ i.val < c := by
  classical
  by_cases hleft : ∀ i, (f i).val < b
  · exact Or.inl hleft
  by_cases hright : ∀ i, b ≤ (f i).val
  · exact Or.inr (Or.inl hright)
  have hex : ∃ t : ℕ, ∃ ht : t < k, b ≤ (f ⟨t, ht⟩).val := by
    obtain ⟨i, hi⟩ := not_forall.mp hleft
    exact ⟨i.val, i.isLt, by simpa using (not_lt.mp hi)⟩
  obtain ⟨hck, hcright⟩ := Nat.find_spec hex
  have hcut : ∀ i : Fin k, (f i).val < b ↔ i.val < Nat.find hex := by
    intro i
    constructor
    · intro hi
      by_contra hnot
      have hci : (⟨Nat.find hex, hck⟩ : Fin k) ≤ i := by
        change Nat.find hex ≤ i.val
        omega
      have hmono : (f ⟨Nat.find hex, hck⟩).val ≤ (f i).val := f.monotone hci
      omega
    · intro hi
      by_contra hnot
      have hfi : b ≤ (f i).val := not_lt.mp hnot
      exact Nat.find_min hex hi ⟨i.isLt, by simpa using hfi⟩
  have hc0 : 0 < Nat.find hex := by
    obtain ⟨i, hi⟩ := not_forall.mp hright
    have hil : (f i).val < b := not_le.mp hi
    have hic := (hcut i).mp hil
    omega
  exact Or.inr (Or.inr ⟨Nat.find hex, hc0, hck, hcut⟩)

end StanleyWilf
