import Mathlib
import AnalyticCombinatorics.Ch1.OGF.Defs

/-! # Injective graded products and supermultiplicative counting -/

namespace StanleyWilf

open AnalyticCombinatorics.Ch1

/-- Natural-number supermultiplicativity; the zero index is included. -/
def Supermultiplicative (a : ℕ → ℕ) : Prop :=
  ∀ m n, a m * a n ≤ a (m + n)

/-- A size-preserving, fixed-size injective binary constructor.

No claim is made that every combinatorial class admits one. -/
structure GradedProduct (C : CombClass) where
  join : ∀ m n, C.Obj m × C.Obj n → C.Obj (m + n)
  injective : ∀ m n, Function.Injective (join m n)

theorem GradedProduct.counts_supermultiplicative {C : CombClass}
    (P : GradedProduct C) : Supermultiplicative C.counts := by
  intro m n
  simpa only [CombClass.counts, Fintype.card_prod] using
    Fintype.card_le_of_injective (P.join m n) (P.injective m n)

/-- Empty and singleton objects plus a constructor give objects at every size. -/
theorem one_le_all_of_supermultiplicative {a : ℕ → ℕ}
    (h : Supermultiplicative a) (h0 : 1 ≤ a 0) (h1 : 1 ≤ a 1) :
    ∀ n, 1 ≤ a n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    calc
      1 = 1 * 1 := rfl
      _ ≤ a n * a 1 := Nat.mul_le_mul ih h1
      _ ≤ a (n + 1) := h n 1

/-- The repeated-block estimate in the elementary proof of Fekete. -/
theorem pow_le_mul_index {a : ℕ → ℕ} (h : Supermultiplicative a)
    (h0 : 1 ≤ a 0) (m q : ℕ) : a m ^ q ≤ a (q * m) := by
  induction q with
  | zero => simpa using h0
  | succ q ih =>
    simpa only [pow_succ, Nat.succ_mul] using
      (Nat.mul_le_mul_right (a m) ih).trans (h (q * m) m)

/-- The exact division-with-remainder lower bound; it is valid even at `m = 0`. -/
theorem pow_div_le {a : ℕ → ℕ} (h : Supermultiplicative a)
    (hpos : ∀ n, 1 ≤ a n) (m n : ℕ) : a m ^ (n / m) ≤ a n := by
  have hblock := pow_le_mul_index h (hpos 0) m (n / m)
  have hres : a (n / m * m) ≤ a (n / m * m) * a (n % m) := by
    calc
      a (n / m * m) = a (n / m * m) * 1 := by simp
      _ ≤ a (n / m * m) * a (n % m) := Nat.mul_le_mul_left _ (hpos _)
  have hdecomp : n / m * m + n % m = n := by
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div n m
  have htotal := hblock.trans (hres.trans (h (n / m * m) (n % m)))
  simpa only [hdecomp] using htotal

end StanleyWilf
