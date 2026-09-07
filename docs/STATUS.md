# Verification ledger

## Machine-verification status

- Lean compiler available during authoring: **no**.
- New Lean files compiled: **no**.
- New declarations checked by the Lean kernel: **no**.
- `#print axioms` executed: **no**.
- GitHub remote created/pushed: **no**.

Do not interpret the lack of textual proof placeholders as a successful build.
The finite Python regression tests check independent executable models, not the
Lean parser, elaborator, or kernel.

## Stages

The initial source and exact remaining milestones are recorded as files are
added. No top-level claim of a completed Stanley–Wilf formalization is made.

### Source written (compilation still pending)

- `Permutation/Basic.lean`: occurrences, containment reflexivity/transitivity,
  size monotonicity, hereditary avoidance, the concrete `avoidanceClass`.
- `Permutation/Cuts.lean`: direct/skew cuts and the indecomposability dichotomy.
- `Permutation/BlockSum.lean`: actual direct/skew block permutations and
  fixed-size injectivity for both operations.
- `Symbolic/WeightedSequence.lean`: uniqueness of a fixed-weight cut and
  injectivity of size-graded sequence concatenation.
- `Symbolic/Specification.lean`: an explicit size-wise `C ≃ SEQ(I)` interface,
  transported to the existing library's formal identity `C(z)(1-I(z))=1`.

### Concrete combinatorial obligations still open

1. Establish the numeric ordering lemmas for the two block constructors.
2. Split a pattern occurrence at the boundary between blocks.
3. Prove direct/skew closure of avoiders under the respective indecomposability
   hypothesis, using that split.
4. Restrict the actual block constructors to avoidance subtypes.
5. Construct unique indecomposable factorization and its inverse, including
   the empty sequence and exclusion of zero-size components.
6. Construct the concrete `SequenceSpecification` (not just its interface).
