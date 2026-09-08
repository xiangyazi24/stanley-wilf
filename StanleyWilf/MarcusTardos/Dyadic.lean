import Mathlib

/-!
# Dyadic counting bounds

This file isolates the natural-number arithmetic behind the dyadic counting
step in the Marcus--Tardos argument.  A monotone counting sequence whose value
at `2 * n` is controlled by its value at `n` has a uniform exponential bound.

The proof pads an arbitrary positive size `n` to twice
`(n + 1) / 2`.  Strong induction therefore gives the same estimate as padding
to the next power of two, while avoiding logarithms and their boundary cases.
-/

namespace StanleyWilf.MarcusTardos

/-- A monotone sequence satisfying the Marcus--Tardos doubling recurrence is
bounded at every positive index by `2 * 15 ^ (2 * C * n)`.

The factor `2` comes from the initial estimate at size one.  The factor `2` in
the exponent absorbs the padding of an arbitrary size to an even size. -/
theorem count_le_two_mul_fifteen_pow_of_doubling
    (T : ℕ → ℕ) (C : ℕ)
    (h_one : T 1 ≤ 2)
    (h_double : ∀ n, T (2 * n) ≤ T n * 15 ^ (C * n))
    (h_mono : Monotone T) :
    ∀ n, 1 ≤ n → T n ≤ 2 * 15 ^ (2 * C * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hn_one : n = 1
      · subst n
        calc
          T 1 ≤ 2 := h_one
          _ = 2 * 1 := by simp
          _ ≤ 2 * 15 ^ (2 * C * 1) :=
            Nat.mul_le_mul_left 2 (Nat.one_le_pow _ _ (by norm_num))
      · have hn_two : 2 ≤ n := by omega
        let m := (n + 1) / 2
        have hm_pos : 1 ≤ m := by
          dsimp [m]
          omega
        have hm_lt : m < n := by
          dsimp [m]
          omega
        have hn_le : n ≤ 2 * m := by
          dsimp [m]
          omega
        have hthree : 3 * m ≤ 2 * n := by
          dsimp [m]
          omega
        have hexponent : 2 * C * m + C * m ≤ 2 * C * n := by
          have hscaled := Nat.mul_le_mul_left C hthree
          calc
            2 * C * m + C * m = C * (3 * m) := by ring
            _ ≤ C * (2 * n) := hscaled
            _ = 2 * C * n := by ring
        calc
          T n ≤ T (2 * m) := h_mono hn_le
          _ ≤ T m * 15 ^ (C * m) := h_double m
          _ ≤ (2 * 15 ^ (2 * C * m)) * 15 ^ (C * m) :=
            Nat.mul_le_mul_right _ (ih m hm_lt hm_pos)
          _ = 2 * 15 ^ (2 * C * m + C * m) := by
            rw [pow_add]
            simp only [Nat.mul_assoc]
          _ ≤ 2 * 15 ^ (2 * C * n) :=
            Nat.mul_le_mul_left 2
              (Nat.pow_le_pow_right (by norm_num) hexponent)

/-- Uniform exponential form of the dyadic counting estimate, including the
zero index.  Under the stated recurrence and monotonicity assumptions, the
explicit base `2 * 15 ^ (2 * C)` works for every natural-number index. -/
theorem count_le_uniform_exponential_of_doubling
    (T : ℕ → ℕ) (C : ℕ)
    (h_zero : T 0 ≤ 1)
    (h_one : T 1 ≤ 2)
    (h_double : ∀ n, T (2 * n) ≤ T n * 15 ^ (C * n))
    (h_mono : Monotone T) :
    ∀ n, T n ≤ (2 * 15 ^ (2 * C)) ^ n := by
  intro n
  cases n with
  | zero => simpa using h_zero
  | succ n =>
      have hpositive : 1 ≤ n + 1 := by omega
      have hcount := count_le_two_mul_fifteen_pow_of_doubling
        T C h_one h_double h_mono (n + 1) hpositive
      have htwo : 2 ≤ 2 ^ (n + 1) := by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2)
          (show 1 ≤ n + 1 by omega)
        simpa using this
      calc
        T (n + 1) ≤ 2 * 15 ^ (2 * C * (n + 1)) := hcount
        _ ≤ 2 ^ (n + 1) * 15 ^ (2 * C * (n + 1)) :=
          Nat.mul_le_mul_right _ htwo
        _ = (2 * 15 ^ (2 * C)) ^ (n + 1) := by
          rw [Nat.mul_pow, pow_mul]

end StanleyWilf.MarcusTardos
