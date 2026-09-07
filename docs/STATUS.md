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

### Second-pass combinatorial source (compilation still pending)

- `Permutation/BlockSum.lean`: numeric formulas, relative order within blocks,
  and strict separation across blocks, for both actual operations.
- `Permutation/Positions.lean`: restriction to the first/second position block;
  `positions_split` uses the first selected position in the right block to
  prove an exact preimage-cut equivalence, including empty-domain cases.
- `Permutation/Closure.lean`: occurrence trichotomies and concrete direct/skew
  avoidance closure. Cross-block occurrences produce an actual forbidden-pattern cut.
- `Permutation/AvoidanceProduct.lean`: actual constructors on avoidance
  subtypes; one is selected from the proved indecomposability dichotomy.
  `avoiderCount_supermultiplicative` has **no constructor hypothesis**.
- `Permutation/SmallPatterns.lean`: actual empty/singleton occurrences and
  zero avoider counts at positive indices for pattern length at most one.

### Concrete symbolic obligations still open

1. Construct unique indecomposable factorization and its inverse, including
   the empty sequence and exclusion of zero-size components.
2. Construct the concrete `SequenceSpecification` (not just its interface).
   The current root-limit source uses the binary constructor directly; it must
   not be described as an implemented concrete `Av(τ) ≃ SEQ(I)` equivalence.

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
  `growthTarget_of_product` with both substantive inputs explicit. The new
  `stanleyWilf_of_marcusTardos` supplies the product and handles lengths 0/1;
  its **only mathematical hypothesis** is `MarcusTardosBound τ`.
- `Audit.lean`: kernel-axiom queries, to be executed only after a successful
  build. No printed axiom results are claimed at this point.

### Remaining analytic/final obligations

3. Compile and repair all source before calling any declaration verified.
4. Supply a formal Marcus–Tardos proof or keep its bound explicitly quantified
   in the final relative theorem. A new custom axiom is not an acceptable substitute.
5. Optionally add the supremum characterization and Cauchy–Hadamard radius
   identification. No simple-pole/asymptotic-equivalent claim is made.

## Checks actually executed on the second pass

- Source hygiene: PASS (90 named declarations across 15 Lean files).
- Verification-harness Python unit tests: PASS (11 cases).
- Shell and Python syntax checks: PASS.
- Previous exact finite regression: PASS, with 256 additional coefficient checks
  of `C(z)(1-I(z)) = 1` for the actual selected indecomposable-avoider classes.
- New occurrence regression: PASS; see `occurrence-regression.json`.
  - 10,240 increasing position selections with boundaries, including beyond-end boundaries.
  - 4,424 direct/skew constructor pairs with total size at most 6.
  - 254,258 individual occurrences, including empty occurrences and empty blocks.
  - 29,762 crossing occurrences with an explicitly checked nontrivial cut.
  - Two counterexamples confirm closure is false without the relevant indecomposability.
- Lean/Lake is still unavailable. Both direct download and DNS resolution for
  the public toolchain download failed. No compiler or kernel audit was run.
- The GitHub connector returned 404 for `xiangyazi24/stanley-wilf`; its discovered
  action set exposes reads, not repository creation or pushing. No authenticated
  GitHub CLI is available in the authoring container.

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
