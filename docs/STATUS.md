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

### Analytic source written (compilation still pending)

- `Counting.lean`: an explicit `GradedProduct` interface, the cardinality
  inequality, positivity from sizes zero/one, repeated-block and remainder
  bounds.
- `Analysis/Growth.lean`: negative-log subadditivity, the normalized lower
  bound, and `exists_growthRate` using mathlib's actual Fekete theorem followed
  by continuity of the exponential. Assumptions: strict positivity,
  supermultiplicativity, and a finite exponential upper bound.
- `Interface.lean`: `MarcusTardosBound` as an unasserted proposition, the
  concrete `GrowthTarget`, small-size avoider positivity, and
  `growthTarget_of_product` with both substantive inputs explicit.
- `Audit.lean`: kernel-axiom queries, to be executed only after a successful
  build. No printed axiom results are claimed at this point.

### Remaining analytic/final obligations

7. Compile and repair all initial source before calling any declaration verified.
8. Connect the actual avoidance constructor to `growthTarget_of_product`.
9. Prove the one-element-pattern case (the positive-count log theorem does not
   apply to it), and state the final theorem for nonempty patterns.
10. Supply a formal Marcus–Tardos proof or keep its bound explicitly quantified
    in the final relative theorem. A new custom axiom is not an acceptable substitute.
11. Optionally add the supremum characterization and Cauchy–Hadamard radius
    identification. No simple-pole/asymptotic-equivalent claim is made.

## Checks actually executed on the initial source

- Source hygiene: PASS (58 named declarations across 11 Lean files).
- Verification-harness Python unit tests: PASS (11 cases).
- Shell syntax (`bash -n`): PASS.
- Python syntax (`py_compile`): PASS.
- Exact finite regression: PASS; full results in `finite-regression.json`.
  - All 5,914 permutations of sizes 0 through 7: cut dichotomy.
  - 11,828 direct/skew all-cut decompositions reconstructed correctly.
  - 29,000 constructor input pairs: fixed-size injectivity.
  - 32 forbidden patterns of lengths 2, 3, and 4; 244,762 applicable
    avoidance-closure instances and 1,152 counting inequalities.
  - 963 positive-weight word pairs: fixed-weight concatenation injectivity.
  - Singleton forbidden pattern: counts `[1,0,0,0,0,0,0,0]`.
  - Negative examples checked: unrestricted concatenation is not injective;
    zero-weight atoms invalidate uniqueness of a cut by weight.
- Full `scripts/check.sh`: exited **127**, as intended when `lake` is missing.
  Its source/Python checks passed first; compilation and axiom audit were NOT run.

These outcomes do not certify the Lean source. The first remaining action is
still a real Lean build and any resulting elaboration/API corrections.
