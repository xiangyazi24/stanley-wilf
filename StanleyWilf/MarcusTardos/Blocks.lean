import StanleyWilf.MarcusTardos.Matrix

/-!
# Block decompositions of zero-one matrices

This file formalizes the block geometry used in Section 2 of Marcus and
Tardos' proof of the Füredi--Hajnal conjecture.  A square matrix of side
`q * b` is partitioned into a `q × q` array of square blocks of side `b`.
The nonempty-block contraction records which blocks contain a one-entry.

The central result is the content of Lemma 4 in the paper: if the contraction
contains a permutation matrix, then the original matrix contains the same
permutation matrix.  The permutation-matrix hypothesis is essential; the
statement is false for a general zero-one pattern with repeated one-entries in
a row or column.
-/

namespace StanleyWilf.MarcusTardos

/-- The global coordinate in block `i` corresponding to the local coordinate
`r`.  Blocks are laid out consecutively, so its value is `r + b * i`. -/
def blockCoordinate {q b : ℕ} (i : Fin q) (r : Fin b) : Fin (q * b) :=
  finProdFinEquiv (i, r)

@[simp]
theorem blockCoordinate_val {q b : ℕ} (i : Fin q) (r : Fin b) :
    (blockCoordinate i r).val = r.val + b * i.val := by
  rfl

/-- The block containing a global coordinate. -/
def blockNumber {q b : ℕ} (x : Fin (q * b)) : Fin q :=
  (finProdFinEquiv.symm x).1

/-- The local coordinate of a global coordinate inside its block. -/
def localCoordinate {q b : ℕ} (x : Fin (q * b)) : Fin b :=
  (finProdFinEquiv.symm x).2

@[simp]
theorem blockNumber_blockCoordinate {q b : ℕ} (i : Fin q) (r : Fin b) :
    blockNumber (blockCoordinate i r) = i := by
  simp [blockNumber, blockCoordinate]

@[simp]
theorem localCoordinate_blockCoordinate {q b : ℕ} (i : Fin q) (r : Fin b) :
    localCoordinate (blockCoordinate i r) = r := by
  simp [localCoordinate, blockCoordinate]

@[simp]
theorem blockCoordinate_blockNumber_localCoordinate {q b : ℕ}
    (x : Fin (q * b)) :
    blockCoordinate (blockNumber x) (localCoordinate x) = x := by
  exact finProdFinEquiv.apply_symm_apply x

/-- The `(i,j)` block of a square matrix whose side is `q * b`, represented in
local `b × b` coordinates. -/
def block {q b : ℕ} (A : ZeroOneMatrix (q * b) (q * b))
    (i j : Fin q) : ZeroOneMatrix b b :=
  Finset.univ.filter fun p ↦
    (blockCoordinate i p.1, blockCoordinate j p.2) ∈ A

@[simp]
theorem mem_block {q b : ℕ} (A : ZeroOneMatrix (q * b) (q * b))
    (i j : Fin q) (r c : Fin b) :
    (r, c) ∈ block A i j ↔
      (blockCoordinate i r, blockCoordinate j c) ∈ A := by
  simp [block]

/-- The contraction which places a one at `(i,j)` exactly when the
corresponding block of the original matrix is nonempty. -/
def blockContraction {q b : ℕ} (A : ZeroOneMatrix (q * b) (q * b)) :
    ZeroOneMatrix q q :=
  Finset.univ.filter fun p ↦ (block A p.1 p.2).Nonempty

@[simp]
theorem mem_blockContraction {q b : ℕ}
    (A : ZeroOneMatrix (q * b) (q * b)) (i j : Fin q) :
    (i, j) ∈ blockContraction A ↔ (block A i j).Nonempty := by
  simp [blockContraction]

/-- The local columns in which a square zero-one matrix has a one-entry. -/
def occupiedColumns {b : ℕ} (S : ZeroOneMatrix b b) : Finset (Fin b) :=
  S.image Prod.snd

/-- The local rows in which a square zero-one matrix has a one-entry. -/
def occupiedRows {b : ℕ} (S : ZeroOneMatrix b b) : Finset (Fin b) :=
  S.image Prod.fst

/-- A block is `k`-wide if its one-entries occupy at least `k` distinct
columns. -/
def Wide {b : ℕ} (k : ℕ) (S : ZeroOneMatrix b b) : Prop :=
  k ≤ (occupiedColumns S).card

/-- A block is `k`-tall if its one-entries occupy at least `k` distinct rows. -/
def Tall {b : ℕ} (k : ℕ) (S : ZeroOneMatrix b b) : Prop :=
  k ≤ (occupiedRows S).card

/-- A block is nonempty exactly when it contains a local coordinate whose
corresponding global entry is one. -/
theorem block_nonempty_iff {q b : ℕ}
    (A : ZeroOneMatrix (q * b) (q * b)) (i j : Fin q) :
    (block A i j).Nonempty ↔
      ∃ r c : Fin b, (blockCoordinate i r, blockCoordinate j c) ∈ A := by
  simp only [Finset.nonempty_iff_ne_empty, block]
  simp

/-- Strictly ordered block indices remain strictly ordered after arbitrary
local coordinates are inserted into their blocks. -/
theorem blockCoordinate_lt {q b : ℕ} {i j : Fin q} (hij : i < j)
    (r s : Fin b) : blockCoordinate i r < blockCoordinate j s := by
  change r.val + b * i.val < s.val + b * j.val
  have hij' : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
  have hmul : b * i.val + b ≤ b * j.val := by
    calc
      b * i.val + b = b * (i.val + 1) := by simp [Nat.mul_add]
      _ ≤ b * j.val := Nat.mul_le_mul_left b hij'
  omega

/-- Containment of a permutation matrix in the nonempty-block contraction
lifts to containment in the original matrix.  This is Marcus--Tardos Lemma 4. -/
theorem matrixContains_permutationMatrix_of_blockContraction
    {k q b : ℕ} (tau : Perm k)
    (A : ZeroOneMatrix (q * b) (q * b))
    (h : MatrixContains (permutationMatrix tau) (blockContraction A)) :
    MatrixContains (permutationMatrix tau) A := by
  classical
  obtain ⟨rows, cols, hcontains⟩ := h
  have hblock : ∀ i : Fin k,
      (block A (rows i) (cols (tau i))).Nonempty := by
    intro i
    rw [← mem_blockContraction]
    exact hcontains (i, tau i) (by simp)
  choose point hpoint using hblock
  let liftedRows : Fin k → Fin (q * b) := fun i ↦
    blockCoordinate (rows i) (point i).1
  let liftedCols : Fin k → Fin (q * b) := fun j ↦
    blockCoordinate (cols j) (point (tau.symm j)).2
  have hrows : StrictMono liftedRows := by
    intro i j hij
    exact blockCoordinate_lt (rows.strictMono hij) _ _
  have hcols : StrictMono liftedCols := by
    intro i j hij
    exact blockCoordinate_lt (cols.strictMono hij) _ _
  refine ⟨OrderEmbedding.ofStrictMono liftedRows hrows,
    OrderEmbedding.ofStrictMono liftedCols hcols, ?_⟩
  intro p hp
  rcases p with ⟨i, j⟩
  have hp' : j = tau i := (mem_permutationMatrix tau i j).mp hp
  subst j
  have hlocal := (mem_block A (rows i) (cols (tau i))
    (point i).1 (point i).2).mp (hpoint i)
  simpa [liftedRows, liftedCols] using hlocal

/-- If the original matrix avoids a permutation matrix, then its nonempty-block
contraction avoids that permutation matrix. -/
theorem blockContraction_avoids_permutationMatrix
    {k q b : ℕ} (tau : Perm k)
    (A : ZeroOneMatrix (q * b) (q * b))
    (hA : MatrixAvoids (permutationMatrix tau) A) :
    MatrixAvoids (permutationMatrix tau) (blockContraction A) := by
  intro h
  exact hA (matrixContains_permutationMatrix_of_blockContraction tau A h)

/-- Alias for the direction of Marcus--Tardos Lemma 4 used by coarsening
arguments: avoidance is preserved by nonempty-block contraction. -/
theorem coarsen_avoids {k q b : ℕ} (tau : Perm k)
    (A : ZeroOneMatrix (q * b) (q * b))
    (hA : MatrixAvoids (permutationMatrix tau) A) :
    MatrixAvoids (permutationMatrix tau) (blockContraction A) :=
  blockContraction_avoids_permutationMatrix tau A hA

/-! ### Weight decomposition -/

/-- A square block of side `b` has at most `b²` one-entries. -/
theorem weight_block_le {q b : ℕ}
    (A : ZeroOneMatrix (q * b) (q * b)) (i j : Fin q) :
    weight (block A i j) ≤ b * b := by
  calc
    weight (block A i j) ≤ (Finset.univ : Finset (Fin b × Fin b)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = b * b := by simp

/-- The one-entries of the original matrix lying in a specified block, kept
in global coordinates. -/
def entriesInBlock {q b : ℕ} (A : ZeroOneMatrix (q * b) (q * b))
    (i j : Fin q) : ZeroOneMatrix (q * b) (q * b) :=
  A.filter fun p ↦ blockNumber p.1 = i ∧ blockNumber p.2 = j

@[simp]
theorem mem_entriesInBlock {q b : ℕ}
    (A : ZeroOneMatrix (q * b) (q * b)) (i j : Fin q)
    (r c : Fin (q * b)) :
    (r, c) ∈ entriesInBlock A i j ↔
      (r, c) ∈ A ∧ blockNumber r = i ∧ blockNumber c = j := by
  simp [entriesInBlock]

/-- Passing between local and global coordinates preserves the number of
one-entries in an individual block. -/
theorem weight_block_eq_entriesInBlock {q b : ℕ}
    (A : ZeroOneMatrix (q * b) (q * b)) (i j : Fin q) :
    weight (block A i j) = weight (entriesInBlock A i j) := by
  classical
  apply Finset.card_bij
      (fun p _ ↦ (blockCoordinate i p.1, blockCoordinate j p.2))
  · intro p hp
    rw [mem_entriesInBlock]
    exact ⟨(mem_block A i j p.1 p.2).mp hp, by simp⟩
  · intro p hp r hr hpr
    apply Prod.ext
    · have h : blockCoordinate i p.1 = blockCoordinate i r.1 :=
        congrArg Prod.fst hpr
      have hpair : (i, p.1) = (i, r.1) :=
        (@finProdFinEquiv q b).injective h
      exact congrArg (fun x : Fin q × Fin b ↦ x.2) hpair
    · have h : blockCoordinate j p.2 = blockCoordinate j r.2 :=
        congrArg Prod.snd hpr
      have hpair : (j, p.2) = (j, r.2) :=
        (@finProdFinEquiv q b).injective h
      exact congrArg (fun x : Fin q × Fin b ↦ x.2) hpair
  · intro p hp
    rw [mem_entriesInBlock] at hp
    refine ⟨(localCoordinate p.1, localCoordinate p.2), ?_, ?_⟩
    · rw [mem_block]
      have hrow : blockCoordinate i (localCoordinate p.1) = p.1 := by
        rw [← hp.2.1]
        exact blockCoordinate_blockNumber_localCoordinate p.1
      have hcol : blockCoordinate j (localCoordinate p.2) = p.2 := by
        rw [← hp.2.2]
        exact blockCoordinate_blockNumber_localCoordinate p.2
      simpa [hrow, hcol] using hp.1
    · apply Prod.ext
      · rw [← hp.2.1]
        exact blockCoordinate_blockNumber_localCoordinate p.1
      · rw [← hp.2.2]
        exact blockCoordinate_blockNumber_localCoordinate p.2

/-- Matrix weight is the sum of the weights of all blocks. -/
theorem weight_eq_sum_block_weights {q b : ℕ}
    (A : ZeroOneMatrix (q * b) (q * b)) :
    weight A = ∑ i : Fin q, ∑ j : Fin q, weight (block A i j) := by
  classical
  let locate : Fin (q * b) × Fin (q * b) → Fin q × Fin q :=
    fun p ↦ (blockNumber p.1, blockNumber p.2)
  have hpartition :
      weight A = ∑ ij : Fin q × Fin q,
        weight (entriesInBlock A ij.1 ij.2) := by
    simpa only [weight, entriesInBlock, locate, Prod.ext_iff] using
      (Finset.card_eq_sum_card_fiberwise
        (f := locate) (s := A) (t := (Finset.univ : Finset (Fin q × Fin q)))
        (by intro p hp; simp))
  rw [hpartition]
  simp_rw [← weight_block_eq_entriesInBlock A]
  rw [← Finset.univ_product_univ, Finset.sum_product]

end StanleyWilf.MarcusTardos
