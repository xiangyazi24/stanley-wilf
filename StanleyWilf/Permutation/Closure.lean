import StanleyWilf.Permutation.BlockSum
import StanleyWilf.Permutation.Cuts
import StanleyWilf.Permutation.Positions

/-!
# Concrete avoidance closure

An occurrence in a block sum either restricts to one input permutation or
induces a nontrivial cut of the forbidden pattern. The two closure theorems
therefore need only the corresponding indecomposability hypothesis.
-/

namespace StanleyWilf

variable {k m n : ℕ}

/-- Pull an occurrence back to a first block with the same relative order. -/
def Occurrence.ofLeftPositions {τ : Perm k} {σ : Perm m} {ρ : Perm (m + n)}
    (e : Occurrence τ ρ) (hf : ∀ i, (e.position i).val < m)
    (hblock : ∀ i j : Fin m,
      ρ (Fin.castAdd n i) < ρ (Fin.castAdd n j) ↔ σ i < σ j) : Occurrence τ σ where
  position := restrictLeft e.position hf
  pattern i j := (e.pattern i j).trans (by
    simpa only [castAdd_restrictLeft] using
      hblock (restrictLeft e.position hf i) (restrictLeft e.position hf j))

/-- Pull an occurrence back to a second block, removing the position offset. -/
def Occurrence.ofRightPositions {τ : Perm k} {π : Perm n} {ρ : Perm (m + n)}
    (e : Occurrence τ ρ) (hf : ∀ i, m ≤ (e.position i).val)
    (hblock : ∀ i j : Fin n,
      ρ (Fin.natAdd m i) < ρ (Fin.natAdd m j) ↔ π i < π j) : Occurrence τ π where
  position := restrictRight e.position hf
  pattern i j := (e.pattern i j).trans (by
    simpa only [natAdd_restrictRight] using
      hblock (restrictRight e.position hf i) (restrictRight e.position hf j))

/-- The full direct-sum occurrence trichotomy, including empty blocks/patterns. -/
theorem contains_directSum_cases {τ : Perm k} {σ : Perm m} {π : Perm n}
    (h : Contains τ (directSum σ π)) :
    Contains τ σ ∨ Contains τ π ∨ SumDecomposable τ := by
  obtain ⟨e⟩ := h
  rcases positions_split e.position m with hleft | hright | ⟨c, hc0, hck, hcut⟩
  · exact Or.inl ⟨e.ofLeftPositions hleft (directSum_left_lt_iff σ π)⟩
  · exact Or.inr (Or.inl ⟨e.ofRightPositions hright (directSum_right_lt_iff σ π)⟩)
  · apply Or.inr
    apply Or.inr
    refine ⟨c, hc0, hck, ?_⟩
    intro i j hi hj
    apply (e.pattern i j).mpr
    apply directSum_cross σ π ((hcut i).mpr hi)
    have hn : ¬ (e.position j).val < m := by
      intro hlt
      have := (hcut j).mp hlt
      omega
    omega

/-- The skew-sum trichotomy has the reverse inequality only across blocks. -/
theorem contains_skewSum_cases {τ : Perm k} {σ : Perm m} {π : Perm n}
    (h : Contains τ (skewSum σ π)) :
    Contains τ σ ∨ Contains τ π ∨ SkewDecomposable τ := by
  obtain ⟨e⟩ := h
  rcases positions_split e.position m with hleft | hright | ⟨c, hc0, hck, hcut⟩
  · exact Or.inl ⟨e.ofLeftPositions hleft (skewSum_left_lt_iff σ π)⟩
  · exact Or.inr (Or.inl ⟨e.ofRightPositions hright (skewSum_right_lt_iff σ π)⟩)
  · apply Or.inr
    apply Or.inr
    refine ⟨c, hc0, hck, ?_⟩
    intro i j hi hj
    apply (e.pattern j i).mpr
    apply skewSum_cross σ π ((hcut i).mpr hi)
    have hn : ¬ (e.position j).val < m := by
      intro hlt
      have := (hcut j).mp hlt
      omega
    omega

/-- Avoidance of a sum-indecomposable pattern is closed under actual direct sum. -/
theorem avoids_directSum {τ : Perm k} {σ : Perm m} {π : Perm n}
    (hτ : SumIndecomposable τ) (hσ : Avoids τ σ) (hπ : Avoids τ π) :
    Avoids τ (directSum σ π) := by
  intro h
  rcases contains_directSum_cases h with hs | hp | hd
  · exact hσ hs
  · exact hπ hp
  · exact hτ hd

/-- Avoidance of a skew-indecomposable pattern is closed under actual skew sum. -/
theorem avoids_skewSum {τ : Perm k} {σ : Perm m} {π : Perm n}
    (hτ : SkewIndecomposable τ) (hσ : Avoids τ σ) (hπ : Avoids τ π) :
    Avoids τ (skewSum σ π) := by
  intro h
  rcases contains_skewSum_cases h with hs | hp | hd
  · exact hσ hs
  · exact hπ hp
  · exact hτ hd

end StanleyWilf
