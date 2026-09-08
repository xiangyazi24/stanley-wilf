# Verification ledger

## Machine-verification status

- Lean compiler available during authoring: **yes**, Lean `v4.29.0` on uisai2.
- New Lean files compiled: **yes**, remote `lake build` completed 8285/8285.
- New declarations checked by the Lean kernel: **yes**.
- `#print axioms` executed: **yes**, 48 declarations audited.
- GitHub remote created/pushed: **yes**.

The absence of textual proof placeholders is not itself a build result. The
current build and axiom-audit evidence is recorded below; the finite Python
regression tests check independent executable models in addition to Lean.

## Stages

The unconditional Stanley--Wilf formalization is kernel-checked.  The
Marcus--Tardos extremal theorem, Klazar counting reduction, and symbolic growth
argument are all connected in the dependency cone of `stanleyWilf`.

### Marcus--Tardos and Klazar source (compiled)

- `ForbiddenMatrix/*`: an attributed Lean 4.29 adaptation of the Apache-2.0
  `YaelDillies/ForbiddenMatrix` proof of the Marcus--Tardos linear extremal
  estimate, including the original explicit constant.
- `MarcusTardos/Matrix.lean` and `PermutationMatrix.lean`: finite-support
  zero-one matrices and the two-way permutation-pattern containment bridge.
- `MarcusTardos/Blocks.lean`: block contraction, occurrence lifting, and exact
  block-weight decomposition.
- `MarcusTardos/ExtremalBridge.lean`: equivalence with the predicate-matrix
  representation and the finite-support linear bound.
- `MarcusTardos/Enumeration.lean`: the exact fifteen-mask encoding, Klazar
  cardinal recurrence, zero-padding injection, and monotonicity.
- `MarcusTardos/Dyadic.lean`: the recurrence-to-uniform-exponential argument,
  including index zero.
- `MarcusTardos/Final.lean`: permutation matrices inject avoiders into avoiding
  zero-one matrices and produce `marcusTardosBound` for every pattern length.

### Source written and compiled

- `Permutation/Basic.lean`: occurrences, containment reflexivity/transitivity,
  size monotonicity, hereditary avoidance, the concrete `avoidanceClass`.
- `Permutation/Cuts.lean`: direct/skew cuts and the indecomposability dichotomy.
- `Permutation/BlockSum.lean`: actual direct/skew block permutations and
  fixed-size injectivity for both operations.
- `Symbolic/WeightedSequence.lean`: uniqueness of a fixed-weight cut and
  injectivity of size-graded sequence concatenation.
- `Symbolic/Specification.lean`: an explicit size-wise `C ≃ SEQ(I)` interface,
  transported to the existing library's formal identity `C(z)(1-I(z))=1`.

### Second-pass combinatorial source (compiled)

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

### Third-pass symbolic source (compiled)

- `Permutation/Boundary.lean`: invariant prefixes, their equivalence to genuine
  sum cuts, the first positive boundary, and uniqueness of that boundary.
  The cut-to-invariant-prefix direction includes an actual finite pigeonhole proof.
- `Permutation/Split.lean`: actual prefix/suffix permutations, their pattern
  occurrences in the original permutation, exact reconstruction, and
  indecomposability of the first prefix.
- `Permutation/Complement.lean`: value complement as an actual permutation,
  complement invariance of containment/avoidance, interchange of direct/skew
  cuts, and the actual direct-to-skew constructor identity.
- `Symbolic/DirectSequence.lean`: injectivity and surjectivity of the concrete
  variable-cut first-component constructor on avoiders. The constructor does
  NOT merely have a fixed-size injectivity theorem.
- `Symbolic/FirstComponent.lean`: a first-component bijection yields an exact
  convolution, equality with the library's SEQ coefficients, and a separate
  proof of supermultiplicativity by truncating that nonnegative convolution.
- `Symbolic/AvoidanceSequence.lean`: transport to actual skew-indecomposable
  avoiders, choose the correct orientation once per pattern, and construct
  `avoidanceSequenceSpecification` with no decomposition input. Its formal
  identity is `avoidance_ogf_mul_one_sub`.
- `Symbolic/Growth.lean`: `stanleyWilf_symbolic_of_marcusTardos` is the relative
  route.  `stanleyWilf_symbolic` and `stanleyWilf` supply the internally proved
  bound and have no hypotheses; lengths 0 and 1 are handled before logarithms.

### Exact boundary of the new SEQ equivalence

The object-level first-component bijection is implemented in source. The
final size-wise `SequenceSpecification.decompose` uses
`Fintype.equivOfCardEq` after the coefficient equality is proved by strong
induction. No canonical full-list evaluation or round-trip theorem for that
chosen cardinality equivalence is claimed. Building a deterministic full
factor-list equivalence is an optional strengthening, not an extra hypothesis
of the source-level OGF or growth theorems.

### Analytic source written and compiled

- `Counting.lean`: an explicit `GradedProduct` interface, the cardinality
  inequality, positivity from sizes zero/one, repeated-block and remainder
  bounds.
- `Analysis/Growth.lean`: negative-log subadditivity, the normalized lower
  bound, and `exists_growthRate` using mathlib's actual Fekete theorem followed
  by continuity of the exponential. Assumptions: strict positivity,
  supermultiplicativity, and a finite exponential upper bound.
- `Interface.lean`: `MarcusTardosBound` as an unasserted proposition, the
  concrete `GrowthTarget`, small-size avoider positivity, and relative assembly
  lemmas. `MarcusTardos.Final` supplies the bound consumed by the unconditional
  public endpoint in `Symbolic/Growth.lean`.
- `Audit.lean`: kernel-axiom queries, executed after the successful remote
  build; all reported axioms are in the permitted transitive set.

### Optional strengthening

1. Add the supremum characterization and Cauchy–Hadamard radius
  identification. No simple-pole/asymptotic-equivalent claim is made.

## Checks executed for the unconditional endpoint

- Remote full build on uisai2 with Lean `v4.29.0`: **PASS**, 8285/8285.
- `tests/Smoke.lean` and `tests/MarcusTardosSmoke.lean`: **PASS**.
- `Audit.lean` plus `scripts/check_axioms.py`: **PASS**, 48 declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Source hygiene: **PASS**, 371 named declarations across 37 Lean files.
- Existing exact Python regression suites: **PASS**.

## Checks actually executed on the fourth pass

- Remote `lake build` on uisai2 with Lean `v4.29.0`: **PASS**, 8272/8272
  targets built.
- `lake env lean tests/Smoke.lean`: **PASS**.
- `Audit.lean` followed by `scripts/check_axioms.py`: **PASS**, 38 declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Source hygiene: **PASS** (183 named declarations across 22 Lean files).
- Python verification harness and all three exact-model suites: **PASS**.
- The Marcus–Tardos exponential bound remains `MarcusTardosBound τ`, an
  explicit theorem input rather than a project axiom.

The third-, second-, and initial-pass sections below are historical records;
their earlier statements about missing compiler access are not the current
verification status.

## Checks actually executed on the third pass

- Source hygiene: PASS (183 named declarations across 22 Lean files).
- New exact models: PASS; see `symbolic-regression.json`.
  - All 46,234 permutations of sizes 0 through 8.
  - 409,113 boundary equivalences and 110,116 actual block reconstructions.
  - 92,466 unique positive first-factor checks, and 92,466 variable-cut
    constructor pairs with both inverse directions checked.
  - 195,162 complement/avoidance equivalences.
  - 33 forbidden patterns, 36 admissible orientations, avoiding sizes through 7.
  - 92,136 avoiding first factors and the same number of avoiding constructor pairs.
  - 288 coefficient recurrences and 1,296 convolution-based count inequalities.
  - 729 arbitrary nonnegative atom sequences, including sparse/periodic examples,
    with 66,339 additional truncated-convolution inequalities.
- Negative tests cover the empty forbidden pattern, empty first components,
  unrestricted concatenation, decomposable forbidden patterns, and the
  alternating zero coefficients of SEQ(Z^2). The last example explains why
  the analytic limit theorem still needs positivity of the avoiding counts.
- All results above concern independent executable finite models, not Lean.
- The authoring container still has no Lean/Lake, and the toolchain download
  failed. No Lean or transitive axiom audit result is claimed.
- The complete `scripts/check.sh` was actually run: source checks, 11 harness
  tests, and all three exact-model suites passed. The script then exited 127
  because `lake` is unavailable. There is no Lean build or axiom result.
- All 20 local library modules are reachable from the root import, without an
  import cycle. 38 transitive axiom queries are prepared, NOT executed.
- Both GitHub `get_repo` and an actual `create_file` publication attempt returned
  404 for the exact target repository. Current connector actions support
  repository writes but not repository creation. No remote mutation succeeded.

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
- The GitHub connector returned 404 for `xiangyazi24/stanley-wilf`; the earlier discovered
  action set exposed reads, not repository creation or pushing. In the third
  pass write actions are available, but repository creation is still absent. No authenticated
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
