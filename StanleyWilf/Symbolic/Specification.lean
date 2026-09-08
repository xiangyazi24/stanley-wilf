import AnalyticCombinatorics.Ch1.OGF.SequenceInverse

/-!
# Transporting the existing symbolic SEQ theorem

The size-wise equivalence below is an explicit input. Establishing it for
indecomposable avoiders is a concrete mathematical obligation, not a field
that can be silently filled by an assumption.
-/

namespace StanleyWilf

open AnalyticCombinatorics.Ch1

/-- A genuine symbolic specification `C ≃ SEQ(I)`, including no zero-size atoms. -/
structure SequenceSpecification (C I : CombClass) where
  noEmptyAtom : I.counts 0 = 0
  decompose : ∀ n, C.Obj n ≃ I.seq.Obj n

namespace SequenceSpecification

variable {C I : CombClass} (S : SequenceSpecification C I)

include S

theorem counts_eq (n : ℕ) : C.counts n = I.seq.counts n :=
  Fintype.card_congr (S.decompose n)

theorem ogf_eq : C.ogf = I.seq.ogf := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.coeff_ogf, S.counts_eq n]

/-- Denominator-cleared formal identity: no analytic convergence claim is hidden here. -/
theorem ogf_mul_one_sub : C.ogf * (1 - I.ogf) = 1 := by
  rw [S.ogf_eq]
  exact CombClass.ogf_seq_mul S.noEmptyAtom

end SequenceSpecification
end StanleyWilf
