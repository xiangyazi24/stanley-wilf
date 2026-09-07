import Mathlib

/-!
# The fixed-size concatenation lemma for SEQ

A word is weighted by the sizes of its components. Strict positivity of
component sizes is essential: it makes the cut at a specified cumulative
size unique. The unrestricted map `(xs,ys) ↦ xs ++ ys` is not injective.
-/

namespace StanleyWilf.WeightedSequence

universe u
variable {α : Type u}

def weight (size : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => size x + weight size xs

@[simp] theorem weight_nil (size : α → ℕ) : weight size [] = 0 := rfl

@[simp] theorem weight_cons (size : α → ℕ) (x : α) (xs : List α) :
    weight size (x :: xs) = size x + weight size xs := rfl

@[simp] theorem weight_append (size : α → ℕ) (xs ys : List α) :
    weight size (xs ++ ys) = weight size xs + weight size ys := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih => simp [weight, ih, Nat.add_assoc]

/-- Equal-weight prefixes of the same word coincide, provided all sizes are positive. -/
theorem append_eq_of_equal_weight (size : α → ℕ) (hpos : ∀ x, 0 < size x)
    (xs ys xs' ys' : List α)
    (hw : weight size xs = weight size xs')
    (happend : xs ++ ys = xs' ++ ys') : xs = xs' ∧ ys = ys' := by
  induction xs generalizing xs' with
  | nil =>
    cases xs' with
    | nil => exact ⟨rfl, by simpa using happend⟩
    | cons b bs =>
      have hb := hpos b
      simp only [weight_nil, weight_cons] at hw
      omega
  | cons a as ih =>
    cases xs' with
    | nil =>
      have ha := hpos a
      simp only [weight_nil, weight_cons] at hw
      omega
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at happend
      obtain ⟨hab, htail⟩ := happend
      subst b
      have hw' : weight size as = weight size bs := by
        simp only [weight_cons] at hw
        omega
      obtain ⟨hxs, hys⟩ := ih bs hw' htail
      exact ⟨congrArg (List.cons a) hxs, hys⟩

abbrev Slice (size : α → ℕ) (n : ℕ) := {xs : List α // weight size xs = n}

def append {size : α → ℕ} {m n : ℕ}
    (x : Slice size m) (y : Slice size n) : Slice size (m + n) :=
  ⟨x.val ++ y.val, by rw [weight_append, x.property, y.property]⟩

/-- The genuine size-graded injectivity used by the symbolic-method proof. -/
theorem append_injective {size : α → ℕ} (hpos : ∀ x, 0 < size x) (m n : ℕ) :
    Function.Injective
      (fun p : Slice size m × Slice size n => append p.1 p.2) := by
  rintro ⟨⟨xs, hx⟩, ⟨ys, hy⟩⟩ ⟨⟨xs', hx'⟩, ⟨ys', hy'⟩⟩ h
  have happend : xs ++ ys = xs' ++ ys' := congrArg Subtype.val h
  have hw : weight size xs = weight size xs' := hx.trans hx'.symm
  obtain ⟨hxs, hys⟩ := append_eq_of_equal_weight size hpos xs ys xs' ys' hw happend
  subst xs'
  subst ys'
  rfl

end StanleyWilf.WeightedSequence
