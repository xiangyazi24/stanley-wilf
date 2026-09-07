# Paper proof and formalization boundary

Let tau be a nonempty permutation pattern, C = Av(tau), and c_n = |C_n|,
including c_0 = 1.

If |tau| = 1, there are no nonempty avoiders, so the desired limit is zero.
Assume |tau| >= 2.

A nontrivial direct-sum decomposition puts every entry of the first block
below every entry of the second. In particular the first entry is below the
last. A nontrivial skew-sum decomposition implies the opposite inequality.
Thus tau cannot be decomposable for both operations. Choose an operation for
which it is indecomposable.

The avoidance class is closed under this operation. An occurrence in a joined
permutation either lies in a single block, contradicting that block's avoidance,
or meets both blocks, inducing a forbidden decomposition of tau.

Let I be the nonempty indecomposable members of C for the chosen operation.
The unique indecomposable decomposition of a permutation gives a size-preserving
bijection C = SEQ(I). This is an unlabelled, size-additive construction; there
is no binomial coefficient for distributing labels. Its ordinary generating
functions satisfy

    C(z) = 1 + I(z) C(z),   C(z)(1-I(z)) = 1.

Every component has strictly positive size. For **fixed** m and n, a
concatenation of two component sequences can be cut back uniquely at cumulative
size m. Consequently

    C_m × C_n -> C_(m+n)

is injective, and c_(m+n) >= c_m c_n. Concatenation with the cut position
unspecified is NOT generally injective.

The singleton belongs to C. Repeated joining shows c_n >= 1 for every n.
The Marcus–Tardos theorem gives a finite K >= 1 such that c_n <= K^n.

Put L = sup_{m>=1} c_m^(1/m), which is at most K. Fix m >= 1 and write
n = qm+r, 0 <= r < m. Supermultiplicativity yields c_n >= c_m^q c_r >= c_m^q.
Thus liminf c_n^(1/n) >= c_m^(1/m). Taking the supremum over m gives liminf
at least L, while every term is at most L. The limit exists and equals L.

Equivalently, Cauchy–Hadamard identifies the limit with the reciprocal radius
of convergence of C. **The identity C = 1/(1-I) alone does not establish a
positive radius**; that is where the Marcus–Tardos bound is used. It also does
not imply that the dominant singularity must be a simple pole or that I(rho)=1.

## What Lean must still establish

The formal proof must connect the concrete avoidance class to the abstract
constructor and sequence interfaces. Supplying an arbitrary `SequenceSpecification`
or `GradedProduct` as a hypothesis is not a proof that avoiders satisfy it.
Likewise the input exponential bound remains an input until a formal
Marcus–Tardos proof is imported or implemented.

The project initially proves the reusable interfaces and the analytic engine;
the concrete closure, unique factorization, and final assembly are separate
milestones, explicitly listed in STATUS.md.
