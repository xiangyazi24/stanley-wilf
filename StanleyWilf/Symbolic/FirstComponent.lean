import StanleyWilf.Symbolic.Specification
import StanleyWilf.Counting
import Mathlib.Data.Fintype.EquivFin

/-!
# From the first-component constructor to the SEQ generating function

A genuine, size-wise first-component bijection `C₊ ≃ I × C`, together with a
unique empty object, determines every coefficient by strong induction. This
is the recursive symbolic specification `C = ε + I × C`.

The final `SequenceSpecification` uses a finite-cardinality equivalence.
Its `decompose` field is NOT asserted to be the canonical factor-list algorithm;
the supplied first-component bijection remains the structural content.
-/

namespace StanleyWilf

open AnalyticCombinatorics.Ch1

structure FirstComponentSpecification (C I : CombClass) where
  noEmptyAtom : I.counts 0 = 0
  emptyCount : C.counts 0 = 1
  split : ∀ n, C.Obj (n + 1) ≃
    (Σ j : Fin (n + 1), I.Obj (j.val + 1) × C.Obj (n - j.val))

namespace FirstComponentSpecification

variable {C I : CombClass} (S : FirstComponentSpecification C I)

/-- The exact convolution obtained from the actual object-level bijection. -/
theorem counts_succ (n : ℕ) :
    C.counts (n + 1) =
      ∑ j : Fin (n + 1), I.counts (j.val + 1) * C.counts (n - j.val) := by
  change Fintype.card (C.Obj (n + 1)) = _
  rw [Fintype.card_congr (S.split n), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact Fintype.card_prod _ _

theorem counts_succ_range (n : ℕ) :
    C.counts (n + 1) =
      ∑ j ∈ Finset.range (n + 1), I.counts (j + 1) * C.counts (n - j) := by
  rw [S.counts_succ]
  exact Fin.sum_univ_eq_sum_range
    (fun j => I.counts (j + 1) * C.counts (n - j)) (n + 1)

/-- Supermultiplicativity follows from the symbolic convolution itself.
The proof truncates the nonnegative convolution and uses strong induction;
there is no separately supplied binary constructor. -/
theorem counts_supermultiplicative : Supermultiplicative C.counts := by
  intro m n
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp only [S.emptyCount, Nat.zero_add, one_mul, le_refl]
    | succ m =>
      calc
        C.counts (m + 1) * C.counts n =
            ∑ j ∈ Finset.range (m + 1),
              (I.counts (j + 1) * C.counts (m - j)) * C.counts n := by
          rw [S.counts_succ_range, Finset.sum_mul]
        _ ≤ ∑ j ∈ Finset.range (m + 1),
              I.counts (j + 1) * C.counts (m + n - j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
          have hrec := ih (m - j) (by omega)
          have heq : m - j + n = m + n - j := by omega
          calc
            (I.counts (j + 1) * C.counts (m - j)) * C.counts n =
                I.counts (j + 1) * (C.counts (m - j) * C.counts n) :=
              Nat.mul_assoc _ _ _
            _ ≤ I.counts (j + 1) * C.counts (m - j + n) :=
              Nat.mul_le_mul_left _ hrec
            _ = I.counts (j + 1) * C.counts (m + n - j) := by rw [heq]
        _ ≤ ∑ j ∈ Finset.range (m + n + 1),
              I.counts (j + 1) * C.counts (m + n - j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          intro j _ _
          exact Nat.zero_le _
        _ = C.counts (m + 1 + n) := by
          rw [show m + 1 + n = m + n + 1 by omega, S.counts_succ_range]

/-- There is no asymptotic step here: all coefficients agree exactly. -/
theorem counts_eq_seq (n : ℕ) : C.counts n = I.seq.counts n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact S.emptyCount.trans (counts_seq_zero (C := I)).symm
    | succ n =>
      rw [S.counts_succ, counts_seq_succ]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (n - j.val) (by omega)]

/-- A size-wise equivalence obtained from the proved equality of finite counts. -/
noncomputable def toSequenceSpecification : SequenceSpecification C I where
  noEmptyAtom := S.noEmptyAtom
  decompose n := Fintype.equivOfCardEq (S.counts_eq_seq n)

/-- The exact symbolic identity, with no Marcus–Tardos or convergence hypothesis. -/
theorem ogf_mul_one_sub : C.ogf * (1 - I.ogf) = 1 :=
  S.toSequenceSpecification.ogf_mul_one_sub

end FirstComponentSpecification
end StanleyWilf
