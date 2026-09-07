import Mathlib
import AnalyticCombinatorics.Ch1.OGF.Defs

/-!
# Permutations, pattern occurrences, and avoidance

An occurrence records an order-preserving selection of positions and the exact
relative order of the selected values. It is not merely an arbitrary embedding
of the underlying finite sets.
-/

namespace StanleyWilf

open AnalyticCombinatorics.Ch1

abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

/-- A classical permutation-pattern occurrence. -/
structure Occurrence {k n : ℕ} (τ : Perm k) (σ : Perm n) where
  position : Fin k ↪o Fin n
  pattern : ∀ i j : Fin k, τ i < τ j ↔ σ (position i) < σ (position j)

variable {k m n : ℕ}

/-- Pattern containment, with the occurrence witness hidden in `Prop`. -/
def Contains (τ : Perm k) (σ : Perm n) : Prop := Nonempty (Occurrence τ σ)

/-- Classical permutation-pattern avoidance. -/
def Avoids (τ : Perm k) (σ : Perm n) : Prop := ¬ Contains τ σ

/-- Every permutation contains itself. -/
def Occurrence.refl (τ : Perm k) : Occurrence τ τ where
  position := OrderEmbedding.refl _
  pattern _ _ := Iff.rfl

/-- Compose selections of positions; relative order is preserved transitively. -/
def Occurrence.trans {ρ : Perm k} {τ : Perm m} {σ : Perm n}
    (h₁ : Occurrence ρ τ) (h₂ : Occurrence τ σ) : Occurrence ρ σ where
  position := h₁.position.trans h₂.position
  pattern i j := (h₁.pattern i j).trans (h₂.pattern _ _)

theorem contains_refl (τ : Perm k) : Contains τ τ := ⟨Occurrence.refl τ⟩

theorem contains_trans {ρ : Perm k} {τ : Perm m} {σ : Perm n}
    (h₁ : Contains ρ τ) (h₂ : Contains τ σ) : Contains ρ σ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

theorem size_le_of_contains {τ : Perm k} {σ : Perm n}
    (h : Contains τ σ) : k ≤ n := by
  obtain ⟨e⟩ := h
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective e.position e.position.injective

theorem avoids_of_size_lt (τ : Perm k) (σ : Perm n)
    (h : n < k) : Avoids τ σ := by
  intro hcontains
  exact (Nat.not_le_of_lt h) (size_le_of_contains hcontains)

/-- Avoidance passes to every contained permutation. -/
theorem avoids_of_contains {τ : Perm k} {σ : Perm m} {π : Perm n}
    (hsub : Contains σ π) (havoid : Avoids τ π) : Avoids τ σ := by
  intro h
  exact havoid (contains_trans h hsub)

abbrev Avoider (τ : Perm k) (n : ℕ) := {σ : Perm n // Avoids τ σ}

/-- Concrete avoidance as the existing symbolic-method library's finite class. -/
noncomputable def avoidanceClass (τ : Perm k) : CombClass where
  Obj n := Avoider τ n
  finObj _ := by
    classical
    infer_instance

noncomputable def avoiderCount (τ : Perm k) (n : ℕ) : ℕ :=
  (avoidanceClass τ).counts n

end StanleyWilf
