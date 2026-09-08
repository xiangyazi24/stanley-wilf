import StanleyWilf.MarcusTardos.PermutationMatrix

/-!
# Enumeration of matrices avoiding a permutation matrix

This file develops the counting side of the Marcus--Tardos argument.  Square
zero-one matrices are cut into consecutive `2 x 2` blocks.  Their contraction
records the nonempty blocks, while a nonempty local mask records one of the
fifteen possible fillings of each occupied block.

The geometric linear bound for permutation-matrix avoidance belongs in a
separate module.  Here it is represented only by the explicitly quantified
predicate `LinearAvoidingMatrixBound`; no instance of that predicate is
postulated.
-/

namespace StanleyWilf.MarcusTardos

/-! ### Avoiding square matrices -/

/-- Square zero-one matrices of side `n` which avoid `P`. -/
abbrev SquareAvoider {k : ℕ} (P : ZeroOneMatrix k k) (n : ℕ) :=
  {A : ZeroOneMatrix n n // MatrixAvoids P A}

/-- The number of square zero-one matrices of side `n` which avoid `P`. -/
noncomputable def avoidingMatrixCount {k : ℕ} (P : ZeroOneMatrix k k)
    (n : ℕ) : ℕ :=
  Nat.card (SquareAvoider P n)

/-- A linear extremal bound for `P`: every avoiding `n x n` matrix has at
most `C * n` one-entries.  This is the output supplied by the geometric part
of the Marcus--Tardos proof. -/
def LinearAvoidingMatrixBound {k : ℕ} (P : ZeroOneMatrix k k) (C : ℕ) : Prop :=
  ∀ n (A : ZeroOneMatrix n n), MatrixAvoids P A → weight A ≤ C * n

/-! ### Consecutive `2 x 2` blocks and contraction -/

/-- Insert a local coordinate in the block with index `i`.  Thus block `i`
occupies the two coordinates `2*i` and `2*i+1`. -/
def twoBlockCoordinate {n : ℕ} (i : Fin n) (r : Fin 2) : Fin (n * 2) :=
  finProdFinEquiv (i, r)

@[simp]
theorem twoBlockCoordinate_val {n : ℕ} (i : Fin n) (r : Fin 2) :
    (twoBlockCoordinate i r).val = r.val + 2 * i.val := by
  rfl

/-- The local `2 x 2` mask in block `(i,j)` of a matrix of side `2*n`. -/
def twoBlock {n : ℕ} (A : ZeroOneMatrix (n * 2) (n * 2))
    (i j : Fin n) : ZeroOneMatrix 2 2 :=
  Finset.univ.filter fun p ↦
    (twoBlockCoordinate i p.1, twoBlockCoordinate j p.2) ∈ A

@[simp]
theorem mem_twoBlock {n : ℕ} (A : ZeroOneMatrix (n * 2) (n * 2))
    (i j : Fin n) (r c : Fin 2) :
    (r, c) ∈ twoBlock A i j ↔
      (twoBlockCoordinate i r, twoBlockCoordinate j c) ∈ A := by
  simp [twoBlock]

/-- The `n x n` matrix whose one-entries are the nonempty `2 x 2` blocks of
the original matrix. -/
def twoBlockContraction {n : ℕ} (A : ZeroOneMatrix (n * 2) (n * 2)) :
    ZeroOneMatrix n n :=
  Finset.univ.filter fun p ↦ (twoBlock A p.1 p.2).Nonempty

@[simp]
theorem mem_twoBlockContraction {n : ℕ}
    (A : ZeroOneMatrix (n * 2) (n * 2)) (i j : Fin n) :
    (i, j) ∈ twoBlockContraction A ↔ (twoBlock A i j).Nonempty := by
  simp [twoBlockContraction]

/-- Coordinates chosen from strictly ordered blocks remain strictly ordered,
independently of their local offsets. -/
theorem twoBlockCoordinate_lt {n : ℕ} {i j : Fin n} (hij : i < j)
    (r s : Fin 2) : twoBlockCoordinate i r < twoBlockCoordinate j s := by
  change r.val + 2 * i.val < s.val + 2 * j.val
  have hij' : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
  omega

/-- If the contraction contains a permutation matrix, choosing one entry in
each selected nonempty block lifts that occurrence to the original matrix. -/
theorem matrixContains_permutationMatrix_of_twoBlockContraction
    {k n : ℕ} (tau : Perm k) (A : ZeroOneMatrix (n * 2) (n * 2))
    (h : MatrixContains (permutationMatrix tau) (twoBlockContraction A)) :
    MatrixContains (permutationMatrix tau) A := by
  classical
  obtain ⟨rows, cols, hcontains⟩ := h
  have hblock : ∀ i : Fin k,
      (twoBlock A (rows i) (cols (tau i))).Nonempty := by
    intro i
    rw [← mem_twoBlockContraction]
    exact hcontains (i, tau i) (by simp)
  choose point hpoint using hblock
  let liftedRows : Fin k → Fin (n * 2) := fun i ↦
    twoBlockCoordinate (rows i) (point i).1
  let liftedCols : Fin k → Fin (n * 2) := fun j ↦
    twoBlockCoordinate (cols j) (point (tau.symm j)).2
  have hrows : StrictMono liftedRows := by
    intro i j hij
    exact twoBlockCoordinate_lt (rows.strictMono hij) _ _
  have hcols : StrictMono liftedCols := by
    intro i j hij
    exact twoBlockCoordinate_lt (cols.strictMono hij) _ _
  refine ⟨OrderEmbedding.ofStrictMono liftedRows hrows,
    OrderEmbedding.ofStrictMono liftedCols hcols, ?_⟩
  rintro ⟨i, j⟩ hp
  have hp' : j = tau i := (mem_permutationMatrix tau i j).mp hp
  subst j
  have hlocal := (mem_twoBlock A (rows i) (cols (tau i))
    (point i).1 (point i).2).mp (hpoint i)
  simpa [liftedRows, liftedCols] using hlocal

/-- Contracting consecutive `2 x 2` blocks preserves avoidance of a
permutation matrix. -/
theorem twoBlockContraction_avoids_permutationMatrix
    {k n : ℕ} (tau : Perm k) (A : ZeroOneMatrix (n * 2) (n * 2))
    (hA : MatrixAvoids (permutationMatrix tau) A) :
    MatrixAvoids (permutationMatrix tau) (twoBlockContraction A) := by
  intro h
  exact hA (matrixContains_permutationMatrix_of_twoBlockContraction tau A h)

/-! ### The fifteen local fillings of an occupied block -/

/-- A nonempty local filling of a `2 x 2` block. -/
abbrev NonemptyTwoMask :=
  {S : ZeroOneMatrix 2 2 // S.Nonempty}

/-- An occupied `2 x 2` block has exactly fifteen possible local fillings. -/
theorem card_nonemptyTwoMask : Fintype.card NonemptyTwoMask = 15 := by
  classical
  have h := Fintype.card_subtype_compl
    (fun S : ZeroOneMatrix 2 2 ↦ S.Nonempty)
  have hall : Fintype.card (ZeroOneMatrix 2 2) = 16 := by
    simp [ZeroOneMatrix, Fintype.card_finset]
  have hempty :
      Fintype.card {S : ZeroOneMatrix 2 2 // ¬ S.Nonempty} = 1 := by
    simp only [Finset.not_nonempty_iff_eq_empty]
    exact Fintype.card_unique
  have hle : Fintype.card NonemptyTwoMask ≤
      Fintype.card (ZeroOneMatrix 2 2) :=
    Fintype.card_subtype_le _
  rw [hempty, hall] at h
  rw [hall] at hle
  have hadd := Nat.sub_add_cancel hle
  rw [← h] at hadd
  omega

/-- Local refinement data for a contraction `B`: one nonempty `2 x 2` mask
for every one-entry of `B`, and no data for its empty blocks. -/
abbrev RefinementData {n : ℕ} (B : ZeroOneMatrix n n) :=
  {p : Fin n × Fin n // p ∈ B} → NonemptyTwoMask

/-- A contraction of weight `w` has exactly `15^w` possible local refinement
records. -/
theorem card_refinementData {n : ℕ} (B : ZeroOneMatrix n n) :
    Fintype.card (RefinementData B) = 15 ^ weight B := by
  classical
  rw [Fintype.card_fun, card_nonemptyTwoMask]
  congr
  simp

/-! ### Encoding by contraction and local masks -/

/-- A matrix of side `2*n` is determined by its complete family of local
`2 x 2` blocks. -/
theorem eq_of_twoBlock_eq {n : ℕ}
    {A A' : ZeroOneMatrix (n * 2) (n * 2)}
    (h : ∀ i j, twoBlock A i j = twoBlock A' i j) : A = A' := by
  ext p
  let ir : Fin n × Fin 2 := finProdFinEquiv.symm p.1
  let jc : Fin n × Fin 2 := finProdFinEquiv.symm p.2
  have hi : twoBlockCoordinate ir.1 ir.2 = p.1 := by
    exact finProdFinEquiv.apply_symm_apply p.1
  have hj : twoBlockCoordinate jc.1 jc.2 = p.2 := by
    exact finProdFinEquiv.apply_symm_apply p.2
  have hm := congrArg (fun S ↦ (ir.2, jc.2) ∈ S) (h ir.1 jc.1)
  simpa [mem_twoBlock, hi, hj] using hm

/-- The dependent code used in Klazar's enumeration argument: an avoiding
contraction together with one of fifteen masks at each occupied block. -/
abbrev AvoiderContractionCode {k : ℕ} (tau : Perm k) (n : ℕ) :=
  Σ B : SquareAvoider (permutationMatrix tau) n, RefinementData B.1

/-- Encode an avoiding matrix by its avoiding contraction and its local
nonempty masks. -/
noncomputable def contractionCodeOfAvoider {k n : ℕ} (tau : Perm k)
    (A : SquareAvoider (permutationMatrix tau) (n * 2)) :
    AvoiderContractionCode tau n :=
  ⟨⟨twoBlockContraction A.1,
      twoBlockContraction_avoids_permutationMatrix tau A.1 A.2⟩,
    fun p ↦ ⟨twoBlock A.1 p.1.1 p.1.2,
      (mem_twoBlockContraction A.1 p.1.1 p.1.2).mp p.2⟩⟩

/-- Reconstruct the global matrix represented by a contraction code.  Empty
blocks contribute no entries; an occupied block is filled by its stored mask. -/
noncomputable def matrixOfContractionCode {k n : ℕ} {tau : Perm k}
    (code : AvoiderContractionCode tau n) :
    ZeroOneMatrix (n * 2) (n * 2) := by
  classical
  exact Finset.univ.filter fun p ↦
    let ir : Fin n × Fin 2 := finProdFinEquiv.symm p.1
    let jc : Fin n × Fin 2 := finProdFinEquiv.symm p.2
    if hp : (ir.1, jc.1) ∈ code.1.1 then
      (ir.2, jc.2) ∈ (code.2 ⟨(ir.1, jc.1), hp⟩).1
    else False

/-- Decoding the contraction code of a matrix recovers the original matrix. -/
theorem matrixOfContractionCode_contractionCodeOfAvoider
    {k n : ℕ} (tau : Perm k)
    (A : SquareAvoider (permutationMatrix tau) (n * 2)) :
    matrixOfContractionCode (contractionCodeOfAvoider tau A) = A.1 := by
  classical
  ext p
  let ir : Fin n × Fin 2 := finProdFinEquiv.symm p.1
  let jc : Fin n × Fin 2 := finProdFinEquiv.symm p.2
  have hi : twoBlockCoordinate ir.1 ir.2 = p.1 := by
    exact finProdFinEquiv.apply_symm_apply p.1
  have hj : twoBlockCoordinate jc.1 jc.2 = p.2 := by
    exact finProdFinEquiv.apply_symm_apply p.2
  by_cases hp : p ∈ A.1
  · have hblock : (ir.1, jc.1) ∈ twoBlockContraction A.1 := by
      rw [mem_twoBlockContraction]
      exact ⟨(ir.2, jc.2), (mem_twoBlock A.1 ir.1 jc.1 ir.2 jc.2).mpr
        (by simpa [hi, hj] using hp)⟩
    have hnonempty : (twoBlock A.1 ir.1 jc.1).Nonempty :=
      (mem_twoBlockContraction A.1 ir.1 jc.1).mp hblock
    have hglobal :
        (twoBlockCoordinate ir.1 ir.2, twoBlockCoordinate jc.1 jc.2) ∈ A.1 := by
      simpa [hi, hj] using hp
    have hiff :
        ((twoBlock A.1 ir.1 jc.1).Nonempty ∧
          (twoBlockCoordinate ir.1 ir.2,
            twoBlockCoordinate jc.1 jc.2) ∈ A.1) ↔ p ∈ A.1 :=
      ⟨fun _ ↦ hp, fun _ ↦ ⟨hnonempty, hglobal⟩⟩
    simpa [matrixOfContractionCode, contractionCodeOfAvoider, ir, jc]
      using hiff
  · have hglobal :
        (twoBlockCoordinate ir.1 ir.2, twoBlockCoordinate jc.1 jc.2) ∉ A.1 := by
      simpa [hi, hj] using hp
    have hiff :
        ((twoBlock A.1 ir.1 jc.1).Nonempty ∧
          (twoBlockCoordinate ir.1 ir.2,
            twoBlockCoordinate jc.1 jc.2) ∈ A.1) ↔ p ∈ A.1 := by
      constructor
      · intro h
        exact (hglobal h.2).elim
      · intro h
        exact (hp h).elim
    simpa [matrixOfContractionCode, contractionCodeOfAvoider, ir, jc]
      using hiff

/-- The Klazar contraction encoding is injective. -/
theorem contractionCodeOfAvoider_injective {k n : ℕ} (tau : Perm k) :
    Function.Injective
      (contractionCodeOfAvoider tau :
        SquareAvoider (permutationMatrix tau) (n * 2) →
          AvoiderContractionCode tau n) := by
  intro A A' h
  apply Subtype.ext
  rw [← matrixOfContractionCode_contractionCodeOfAvoider tau A,
    ← matrixOfContractionCode_contractionCodeOfAvoider tau A', h]

/-- Under a linear weight bound, the set of contraction codes has cardinal at
most the number of avoiding contractions times `15^(C*n)`. -/
theorem card_avoiderContractionCode_le {k n C : ℕ} (tau : Perm k)
    (hlinear : LinearAvoidingMatrixBound (permutationMatrix tau) C) :
    Nat.card (AvoiderContractionCode tau n) ≤
      avoidingMatrixCount (permutationMatrix tau) n * 15 ^ (C * n) := by
  classical
  calc
    Nat.card (AvoiderContractionCode tau n) =
        Fintype.card (AvoiderContractionCode tau n) :=
      Nat.card_eq_fintype_card
    _ = ∑ B : SquareAvoider (permutationMatrix tau) n,
        Fintype.card (RefinementData B.1) :=
      Fintype.card_sigma
    _ ≤
        ∑ _B : SquareAvoider (permutationMatrix tau) n,
          15 ^ (C * n) := by
          apply Finset.sum_le_sum
          intro B _
          rw [card_refinementData]
          exact pow_le_pow_right' (by omega) (hlinear n B.1 B.2)
    _ = avoidingMatrixCount (permutationMatrix tau) n * 15 ^ (C * n) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        avoidingMatrixCount]
      congr 1
      exact (Nat.card_eq_fintype_card).symm

/-- Klazar's `2 x 2` contraction recurrence.  A matrix of side `2*n` is
encoded by an avoiding contraction and at most `C*n` independent nonempty
local masks, each with fifteen choices. -/
theorem avoidingMatrixCount_mul_two_le {k n C : ℕ} (tau : Perm k)
    (hlinear : LinearAvoidingMatrixBound (permutationMatrix tau) C) :
    avoidingMatrixCount (permutationMatrix tau) (n * 2) ≤
      avoidingMatrixCount (permutationMatrix tau) n * 15 ^ (C * n) := by
  calc
    avoidingMatrixCount (permutationMatrix tau) (n * 2) =
        Nat.card (SquareAvoider (permutationMatrix tau) (n * 2)) := rfl
    _ ≤ Nat.card (AvoiderContractionCode tau n) :=
      Nat.card_le_card_of_injective (contractionCodeOfAvoider tau)
        (contractionCodeOfAvoider_injective tau)
    _ ≤ avoidingMatrixCount (permutationMatrix tau) n * 15 ^ (C * n) :=
      card_avoiderContractionCode_le tau hlinear

/-- The same contraction recurrence with the doubled side written as `2*n`. -/
theorem avoidingMatrixCount_two_mul_le {k n C : ℕ} (tau : Perm k)
    (hlinear : LinearAvoidingMatrixBound (permutationMatrix tau) C) :
    avoidingMatrixCount (permutationMatrix tau) (2 * n) ≤
      avoidingMatrixCount (permutationMatrix tau) n * 15 ^ (C * n) := by
  rw [Nat.mul_comm 2 n]
  exact avoidingMatrixCount_mul_two_le tau hlinear

/-! ### Zero padding and monotonicity in the side length -/

/-- Embed an `m x m` matrix into the northwest corner of an `n x n` matrix,
filling all new positions with zero. -/
def zeroPadSquare {m n : ℕ} (hmn : m ≤ n) (A : ZeroOneMatrix m m) :
    ZeroOneMatrix n n :=
  A.map ((Fin.castLEEmb hmn).prodMap (Fin.castLEEmb hmn))

@[simp]
theorem mem_zeroPadSquare {m n : ℕ} (hmn : m ≤ n)
    (A : ZeroOneMatrix m m) (i j : Fin m) :
    (Fin.castLE hmn i, Fin.castLE hmn j) ∈ zeroPadSquare hmn A ↔
      (i, j) ∈ A := by
  simp [zeroPadSquare]

/-- Northwest zero padding is injective. -/
theorem zeroPadSquare_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (zeroPadSquare hmn :
      ZeroOneMatrix m m → ZeroOneMatrix n n) := by
  intro A A' h
  exact Finset.map_injective _ h

/-- If a permutation matrix occurs in a zero-padded matrix, then it already
occurs in the original northwest matrix. -/
theorem matrixContains_of_zeroPadSquare_contains {k m n : ℕ}
    (hmn : m ≤ n) (tau : Perm k) (A : ZeroOneMatrix m m)
    (h : MatrixContains (permutationMatrix tau) (zeroPadSquare hmn A)) :
    MatrixContains (permutationMatrix tau) A := by
  classical
  obtain ⟨rows, cols, hcontains⟩ := h
  have hexists : ∀ i : Fin k, ∃ p ∈ A,
      ((Fin.castLEEmb hmn).prodMap (Fin.castLEEmb hmn)) p =
        (rows i, cols (tau i)) := by
    intro i
    have hi := hcontains (i, tau i) (by simp)
    simpa [zeroPadSquare] using hi
  choose point hpoint hpointEq using hexists
  let liftedRows : Fin k → Fin m := fun i ↦ (point i).1
  let liftedCols : Fin k → Fin m := fun j ↦ (point (tau.symm j)).2
  have hrowEq : ∀ i, Fin.castLE hmn (liftedRows i) = rows i := by
    intro i
    exact congrArg Prod.fst (hpointEq i)
  have hcolEq : ∀ j, Fin.castLE hmn (liftedCols j) = cols j := by
    intro j
    have hj := congrArg Prod.snd (hpointEq (tau.symm j))
    simpa [liftedCols] using hj
  have hrows : StrictMono liftedRows := by
    intro i j hij
    apply (Fin.castLE_lt_castLE_iff hmn).mp
    rw [hrowEq i, hrowEq j]
    exact rows.strictMono hij
  have hcols : StrictMono liftedCols := by
    intro i j hij
    apply (Fin.castLE_lt_castLE_iff hmn).mp
    rw [hcolEq i, hcolEq j]
    exact cols.strictMono hij
  refine ⟨OrderEmbedding.ofStrictMono liftedRows hrows,
    OrderEmbedding.ofStrictMono liftedCols hcols, ?_⟩
  rintro ⟨i, j⟩ hp
  have hj : j = tau i := (mem_permutationMatrix tau i j).mp hp
  subst j
  simpa [liftedRows, liftedCols] using hpoint i

/-- Zero padding preserves avoidance of a permutation matrix. -/
theorem zeroPadSquare_avoids_permutationMatrix {k m n : ℕ}
    (hmn : m ≤ n) (tau : Perm k) (A : ZeroOneMatrix m m)
    (hA : MatrixAvoids (permutationMatrix tau) A) :
    MatrixAvoids (permutationMatrix tau) (zeroPadSquare hmn A) := by
  intro h
  exact hA (matrixContains_of_zeroPadSquare_contains hmn tau A h)

/-- Zero padding gives an injection between avoiding square matrices of
different side lengths. -/
noncomputable def zeroPadAvoider {k m n : ℕ} (hmn : m ≤ n)
    (tau : Perm k) (A : SquareAvoider (permutationMatrix tau) m) :
    SquareAvoider (permutationMatrix tau) n :=
  ⟨zeroPadSquare hmn A.1,
    zeroPadSquare_avoids_permutationMatrix hmn tau A.1 A.2⟩

/-- The number of matrices avoiding a fixed permutation matrix is monotone in
the side length. -/
theorem avoidingMatrixCount_mono {k m n : ℕ} (hmn : m ≤ n)
    (tau : Perm k) :
    avoidingMatrixCount (permutationMatrix tau) m ≤
      avoidingMatrixCount (permutationMatrix tau) n := by
  change Nat.card (SquareAvoider (permutationMatrix tau) m) ≤
    Nat.card (SquareAvoider (permutationMatrix tau) n)
  apply Nat.card_le_card_of_injective (zeroPadAvoider hmn tau)
  intro A A' h
  apply Subtype.ext
  exact zeroPadSquare_injective hmn (congrArg Subtype.val h)

end StanleyWilf.MarcusTardos
