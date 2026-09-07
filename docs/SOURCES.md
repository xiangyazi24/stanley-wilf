# Sources inspected for this initial development

## Pinned Lean source

- AnalyticCombinatorics commit:
  https://github.com/xiangyazi24/AnalyticCombinatorics/tree/3a426641ccfd0add82a82e169083ff97c8d03027
- `AnalyticCombinatorics/Ch1/OGF/Defs.lean`: `CombClass`, `counts`, `ogf`.
- `AnalyticCombinatorics/Ch1/OGF/Sequence.lean`: `CombClass.seq`, positive
  composition-based encoding.
- `AnalyticCombinatorics/Ch1/OGF/SequenceInverse.lean`:
  `CombClass.ogf_seq_functional_eq`, `CombClass.ogf_seq_mul`.
- mathlib's pinned `Mathlib/Analysis/Subadditive.lean`:
  https://github.com/leanprover-community/mathlib4/blob/8a178386ffc0f5fef0b77738bb5449d50efeea95/Mathlib/Analysis/Subadditive.lean
  `Subadditive.tendsto_lim` takes an explicit lower bound on the normalized
  subadditive sequence.

These were inspected as source; this does not establish that the newly written
client code compiles.

## Mathematical references

- Richard Arratia, "On the Stanley–Wilf conjecture for the number of
  permutations avoiding a given pattern", Electronic Journal of Combinatorics
  6 (1999), N1.
  https://www.combinatorics.org/ojs/index.php/eljc/article/view/v6i1n1
- Adam Marcus and Gabor Tardos, "Excluded permutation matrices and the
  Stanley–Wilf conjecture", Journal of Combinatorial Theory, Series A 107
  (2004), 153–160.
  https://web.math.princeton.edu/~amarcus/papers/permmat/MarcusTardos_permmat.pdf
- Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Chapter I:
  the unlabelled sequence construction and ordinary generating functions.

The proof architecture here is an exposition of established mathematics, not a
claim of priority or a new independent proof of Marcus–Tardos.
