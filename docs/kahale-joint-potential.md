# Joint certificate potentials: the first candidate and its barrier

## Summary

Let `z_i` be the minimum zero-certificate size on a wire and `o_i` the minimum
one-certificate size, equivalently the transversal number of its zero family.
We examined a potential using these exact quantities, rather than one selected
certificate or a height upper bound.

The product potential `Q = sum_i z_i o_i` has a sharp factor-two per-stage
upper bound. Its sorting endpoint yields only a leading coefficient `2`.
More generally, **any time-independent additive monomial potential**
`sum_i z_i^p o_i^q`, with positive `p,q`, used through a uniform multiplicative
stage bound cannot yield a leading coefficient greater than `2`.

This rules out a broad elementary candidate class. It does **not** rule out
other potentials, dependence on depth or rank, global constraints, or arguments
using these statistics together with richer information.

We also found and kernel-checked two actual four-wire circuits whose input
statistics agree but whose next statistics differ, even though both comparators
are nonredundant. Minimum certificate size and transversal number do not form
a closed state description: the families' cross-overlaps matter.

## Product potential

For a comparator whose two input statistic pairs are `(a,b)` and `(c,d)`,
the output quantities satisfy

```text
z_min = min(a,c),       o_min <= b+d;
z_max <= a+c,           o_max = min(b,d).
```

The inequalities come from choosing input certificates and taking their unions;
actual unions can be smaller, and alternative choices can be better.
For all nonnegative integer `a,b,c,d`,

\[
\min(a,c)(b+d)+(a+c)\min(b,d)\le2(ab+cd).
\]

Thus a parallel stage has `Q_next <= 2 Q`. Idle wires also satisfy this bound.
Initially `Q=n`. Sorting requires the exact output values
`z_i=i+1`, `o_i=n-i`, giving

\[
Q_{\mathrm{sort}}=\sum_{i=0}^{n-1}(i+1)(n-i)
=\frac{n(n+1)(n+2)}6.
\]

Consequently this potential gives

\[
2^d\ge\frac{(n+1)(n+2)}6,
\qquad d\ge2\log_2 n-O(1).
\]

The factor two is attained by comparing two initially independent inputs:
their pairs `(1,1),(1,1)` become `(1,2),(2,1)`. Therefore a universally smaller
uniform factor for this potential is impossible. This conclusion concerns
this proof scheme, not the sharpness of the actual sorting lower bound.

## Barrier for positive-power monomials

For `Q_(p,q) = sum_i z_i^p o_i^q`, its initial value is `n`, while its sorted
endpoint is `Theta(n^(p+q+1))`. The first parallel stage of disjoint comparisons
has exact growth factor

\[
C_{p,q}=\frac{2^p+2^q}{2}.
\]

Any uniform stage multiplier `C` valid for all networks must satisfy
`C >= C_(p,q)`. A proof that only iterates that multiplier can obtain a leading
coefficient at most

\[
\frac{p+q}{\log_2 C_{p,q}}\le2,
\]

because the arithmetic-geometric mean inequality gives
`C_(p,q) >= 2^((p+q)/2)`. Thus tuning these exponents cannot recover the existing
`3.270559...` coefficient, let alone improve it. This is an analytic exclusion
of a whole candidate class, not a numerical parameter search.

## A concrete failure of the two-number state description

Both examples use standard four-wire comparator networks and Boolean inputs
`x_0,...,x_3`.

### Independent families

First compare `(0,1)` and `(2,3)`, then compare wires `(1,3)`. The last comparator
receives

```text
f = x_0 OR x_1,        g = x_2 OR x_3.
```

Both have `(z,o)=(2,1)`. The outputs have `(2,2)` and `(4,1)`.
The smallest zero certificates of the two inputs are disjoint, so their union
has size four.

### Reconvergent families

First compare `(2,3)`, then `(1,2)`, then `(2,3)`. The last comparator receives

```text
f = x_1 OR (x_2 AND x_3),       g = x_2 OR x_3.
```

Again both have `(z,o)=(2,1)`. This time the outputs have `(2,2)` and `(3,1)`.
The minimal zero certificates of `f` are `{1,2}` and `{1,3}`, while the sole
minimal zero certificate of `g` is `{2,3}`. Their smallest union has size three.

Both final comparators are nonredundant. The difference therefore persists
after ignoring redundant comparisons. These examples are actual reachable
wire functions, not independently chosen Boolean functions that might violate
network conservation.

## Verification

`lake build AKS.Kahale` passes with guarded dependency checks for the product
inequality and the exact small-network examples. No new axioms or external
decision procedures are used.

[`AKS/Kahale/JointPotential.lean`](../AKS/Kahale/JointPotential.lean) contains:

- the universal integer product inequality and its conditional pair bound;
- a computable exact minimum support-size statistic (equivalent to minimum
  certificate size for monotone wire functions);
- kernel-evaluated four-wire examples with identical input statistics and
  different output statistics;
- the two-wire example attaining factor-two product growth.

The product depth corollary and the general real-exponent monomial exclusion
are mathematical derivations here, not additional Lean limit theorems.

[`scripts/kahale_joint_potential.py`](../scripts/kahale_joint_potential.py)
exhausts the reachable Boolean wire-function states on four wires: 261 states
and 45 input-statistic signatures. Its catalogue is stored in
[`kahale-joint-potential-catalogue.json`](kahale-joint-potential-catalogue.json).
This exhaustiveness claim is an exact finite computation, not a kernel proof.
The small counterexamples used in the argument are independently kernel checked.

Reproduce the catalogue with

```sh
python -B scripts/kahale_joint_potential.py
```

## Next target: cross-family overlap

The [suffix-dependent potential experiment](kahale-suffix-potential.md) now
evaluates a Bellman potential on exhaustive three-, four-, and five-wire
catalogues. Pairwise exact union costs remove a remaining-depth information
loss observed for per-wire statistics on five wires. No asymptotic improvement
is established.

**Update:** [the shared-universe coupling](kahale-union-coupling.md) supplies
a universal constraint on the two union costs at an active comparator:
their sum is at most `n+2`. Its rank-crossing and certificate-witness arguments
are formalized separately. This is stronger structure than the uncoupled
union-size estimates, but is not yet an improved asymptotic potential.
The follow-up also proves the suffix-dependent active comparator width bound
`j-i <= 2^(s+1)-1`. This suggests a potential that depends on the remaining
depth and uses global rank requirements, rather than a uniform stage multiplier.

For two incoming zero families, define the union cost

```text
u(Z_a,Z_b) = min {|S union T| : S in Z_a, T in Z_b}.
```

This is the exact minimum zero-certificate size of the max output. Define the
dual quantity for one families and the min output. Unlike the two separate
minimum sizes, these quantities retain the relevant overlap across wires.

A useful next invariant must constrain how frequently both kinds of union
cost can attain their disjoint-set upper bounds throughout one network.
Independent inputs show that overlap loss cannot be demanded at every gate.
It must be forced globally by the shared input universe, conservation, and
the threshold requirements at all output ranks.

Merely recording observed overlap events in our bad schedule is insufficient:
we need an inequality that holds for every sorting network and accumulates
enough loss over logarithmically many stages. No such exponential-rate loss
or improved coefficient has been established yet.
