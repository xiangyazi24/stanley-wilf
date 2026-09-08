# The first-component symbolic route

This is an exposition of established mathematics and a proof map. The Lean
source for the route compiles, but this project does not claim a new proof of
Marcus–Tardos.

## 1. Canonical first component

For a permutation σ of size n, a direct boundary c is an invariant prefix:
σ sends the first c positions into the first c values. Since σ is a finite
bijection, membership in that prefix is reflected as well as preserved.
Thus every value to the left of a nontrivial boundary is below every value to
its right, and this condition is equivalent to the previous `IsSumCut`.

For n > 0, n is a positive boundary. Let c be the least positive boundary.
Restrict σ to the prefix and subtract c from the suffix values to obtain actual
permutations α of size c and β of size n-c. Then σ = α ⊕ β. A smaller direct
cut of α would lift to an earlier boundary of σ, so α is indecomposable.
Conversely, if σ = α ⊕ β with α nonempty and indecomposable, its first positive
boundary has to be |α|. Fixed-cut injectivity then recovers α and β themselves.
This proves a first-factor bijection even when the cut size varies.

When the forbidden pattern τ is sum-indecomposable, the existing closure proof
ensures that joining two avoiding factors still avoids τ. Hereditary avoidance
ensures that the recovered α and β avoid τ. Writing I for the *actual* positive
indecomposable avoiding class, one obtains

    C = ε + I × C,
    c_0 = 1,
    c_(m+1) = sum_(j=0)^m i_(j+1) c_(m-j).

Value complement exchanges direct and skew sums, preserves relative pattern
containment when applied to both permutations, and exchanges the two notions
of indecomposability. It therefore transports the entire first-factor bijection
to actual skew-indecomposable avoiders. Every nonempty τ admits at least one
of these orientations.

## 2. Supermultiplicativity directly from the symbolic recurrence

There is no separately assumed binary constructor in this step. Use strong
induction on m to show c_m c_n <= c_(m+n), for all n. The m=0 case follows from
c_0=1. For the induction step, expand the first factor by the recurrence:

    c_(m+1) c_n
      = sum_(j=0)^m i_(j+1) c_(m-j) c_n
     <= sum_(j=0)^m i_(j+1) c_(m-j+n)
     <= sum_(j=0)^(m+n) i_(j+1) c_(m+n-j)
      = c_(m+n+1).

The first inequality uses the induction hypothesis at m-j. The second only
adds nonnegative terms. This is implemented by
`FirstComponentSpecification.counts_supermultiplicative`.

The same recurrence and initial value hold for the existing library's SEQ(I).
Strong induction therefore gives equality at every coefficient. The library's
formal sequence theorem now yields

    C(z) (1 - I(z)) = 1.

In source, the concluding size-wise `SequenceSpecification` uses a chosen
bijection of finite sets of equal cardinality. It is not represented as a
computed canonical list of factors. The canonical first-factor construction
and its uniqueness are the structural content used before this transport.

## 3. The growth limit

For |τ| >= 2, both sizes zero and one have an avoider. Supermultiplicativity
gives c_n >= 1 for every n. With the explicitly supplied Marcus–Tardos bound
c_n <= K^n, the existing Fekete/logarithm/exponential backend proves a positive
finite limit of c_n^(1/n). For |τ| <= 1, all positive-size counts vanish, and
the limit is zero; no logarithm is used.

The endpoint `stanleyWilf_symbolic τ hMT` therefore depends on the symbolic
first-component recurrence and the explicit bound `hMT`, not the earlier
`avoidanceProduct` proof.

## 4. Essential limitations and side conditions

- The empty forbidden pattern has no avoiders, including at size zero. It
  cannot have a SEQ specification, since SEQ always has an empty sequence.
- Empty permutations satisfy the negated-cut definition of indecomposability,
  so atom classes must explicitly exclude size zero.
- Supermultiplicativity and an exponential bound do not imply convergence of
  nth roots when zero coefficients are allowed. SEQ(Z^2) has coefficients
  1,0,1,0,... . Positivity is separately established for nontrivial avoiders.
- The formal identity does not assert a positive radius of convergence, a
  simple pole, an asymptotic equivalent, or I(ρ)=1.
- The route is now checked by Lean elaboration, compilation, and the
  transitive axiom audit; the Marcus–Tardos bound remains an explicit input.
