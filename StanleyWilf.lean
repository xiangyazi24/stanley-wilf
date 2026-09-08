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
import StanleyWilf.Permutation.Boundary
import StanleyWilf.Permutation.Split
import StanleyWilf.Symbolic.FirstComponent
import StanleyWilf.Symbolic.DirectSequence
import StanleyWilf.Permutation.Complement
import StanleyWilf.Symbolic.AvoidanceSequence
import StanleyWilf.Symbolic.Growth
import StanleyWilf.ForbiddenMatrix.PermutationPatterns
import StanleyWilf.MarcusTardos.Matrix
import StanleyWilf.MarcusTardos.PermutationMatrix
import StanleyWilf.MarcusTardos.Blocks
import StanleyWilf.MarcusTardos.ExtremalBridge
import StanleyWilf.MarcusTardos.Enumeration
import StanleyWilf.MarcusTardos.Dyadic
import StanleyWilf.MarcusTardos.Final

/-!
# Stanley–Wilf

Entry point for the formalization. See README.md and docs/STATUS.md for the
precise verification boundary.  The repository includes the Marcus--Tardos
linear extremal theorem and Klazar's counting reduction, so the public
Stanley--Wilf endpoint is unconditional.
-/
