import StanleyWilf.Counting
import StanleyWilf.Analysis.Growth
import StanleyWilf.Interface
import StanleyWilf.Permutation.Basic
import StanleyWilf.Permutation.Cuts
import StanleyWilf.Permutation.BlockSum
import StanleyWilf.Permutation.Positions
import StanleyWilf.Permutation.Closure
import StanleyWilf.Permutation.AvoidanceProduct
import StanleyWilf.Permutation.SmallPatterns
import StanleyWilf.Symbolic.WeightedSequence
import StanleyWilf.Symbolic.Specification

/-!
# Stanley–Wilf

Entry point for the formalization. See README.md and docs/STATUS.md for the
precise verification boundary. The paper proof uses the established
Marcus–Tardos theorem; this repository does not introduce a corresponding
Lean axiom.
-/
