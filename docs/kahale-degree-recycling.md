# Degree recycling and a cross-weight routing obstruction

## Findings

The proposed local charge from high-degree occupation reserve to scalar
certificate inefficiency fails at arbitrarily large sizes. Two sorted odd
blocks give a comparison of equal-height medians that removes every
nonconstant spectral component of both median signals on the central slice.

There is a more useful cross-weight fact: after sorting the two blocks,
one mirror matching finishes the central slice, but a neighboring slice
still requires at least `ceil(log_2 m)` layers. The central completion has
displaced the remaining routing obligation rather than eliminated it.

These are derived mathematical constructions and exact finite computations,
not new Lean theorems. The proved lower-bound coefficient remains
`3.270559...`. No stronger asymptotic lower bound follows from these examples.

## 1. A comparison that clears all spectral degrees

Let `m` be odd, `n=2m`, and restrict inputs to weight `m`. Sort each
block of `m` wires by identical comparator prefixes. If the first block
contains `a` ones, the second contains `m-a` ones. Their median signals are

```text
f = 1[a >= (m+1)/2],
g = 1[m-a >= (m+1)/2] = 1-f.
```

Comparing the two medians gives `AND(f,g)=0` and `OR(f,g)=1` on this
entire slice. Both input medians have exactly the same scalar height,
because the prefixes are identical. Every nonconstant spectral component
of both signals disappears, irrespective of degree.

This is a reachable ordered-comparator prefix. The explicit finite
probes use insertion sort in each block and validate it on every Boolean
block input for `m=3,5,7`. The two copies run in parallel. The tested
prefixes have depths `3,10,21`, so they are **not witnesses against a
global asymptotic depth tradeoff**. The general construction can use any
correct block sorter. It refutes a universal local penalty at the median
comparison; the cost of preparing the blocks still matters.

### Exact spectral calculation

For functions depending only on `a`, the central-slice Johnson Laplacian is

```text
(L u)(a) = a^2 * (u(a)-u(a-1))
         + (m-a)^2 * (u(a)-u(a+1)).
```

Boundary terms vanish at `a=0,m`. The multiplicity of this coordinate is
`binom(m,a)^2`, not a uniform measure. This formula follows by counting
cross-block swaps; within-block swaps do not change `a`.

On polynomials of degree `r`, the leading coefficient is multiplied by
`r(2m+1-r)`. The invariant polynomial spaces and self-adjointness therefore
give orthogonal eigenpolynomials of degrees `0,...,m`, with these distinct
eigenvalues. The full Johnson spectrum agrees with
[Suzuki's Lemma 7.1](https://icu-hsuzuki.github.io/t-algebra/lec7.html).

The threshold function on `a=0,...,m` has polynomial interpolation degree
exactly `m`: its `m`th finite difference is, up to sign,
`binom(m-1,(m-1)/2)`, which is nonzero. Thus a component at degree
`m=n/2` exists for every odd `m`, and the equal-height gate removes it.

The script recovers spectral squared norms from integer Laplacian moments
and rational Lagrange projectors. Full input-graph calculations for
`n=6,10,14` agree exactly with the compressed block-count calculation.
The latter extends through `n=126` without enumerating all inputs.

| Wires | Block size | Fraction of the median reserve in degrees at least `ceil(m/2)` |
|---:|---:|---:|
| 14 | 7 | 0.6310 |
| 30 | 15 | 0.5132 |
| 62 | 31 | 0.4513 |
| 126 | 63 | 0.4132 |

The reserve weights are `(lambda_r-n)` times the degree-r squared norms.
The table is finite exact rational computation, displayed as rounded
decimals; it does not assert an asymptotic limiting share. The gate clears
all of this reserve without an unequal-height comparison.

## 2. A central slice can finish while its neighbor remains hard

After sorting both blocks, compare wire `i` in the first block with wire
`m-1-i` in the second block, for all `i`. These gates form one disjoint
ordered layer. On weight `m`, each pair contains exactly one one: the
first block's output is `0^m` and the second block's output is `1^m`.
Thus the entire central slice is sorted after that layer. Unlike the
median comparison, this full matching is not claimed to have equal heights.

On weight `m-1`, put `a` ones in the first block and `m-1-a` in the
second. After the same matching, the first block is all zero and the
second block is all one except at wire `m+a`. As `a` ranges from zero
to `m-1`, this zero has every possible position in the second block.

Any sorting suffix must put that zero at wire `m`. Compare these states
with the sorted central-slice state `0^m 1^m`, which every ordered suffix
fixes. Each neighboring state differs from it at exactly one of the `m`
possible wires. The final value at wire `m` must depend on each of those
wires; otherwise the corresponding single-zero case would give the same
one as the central state. A depth-s suffix has at most `2^s` input wires
in an output's dependency cone. Hence

```text
suffix depth >= ceil(log_2 m).
```

The script checks all `m` block-count configurations, including an actual
unsorted output on the neighboring slice. This is a general family-specific
suffix bound, not a universal loss for every short sorting prefix. Its
fanin argument does not itself improve the existing lower bound.

## 3. An exact representation retaining the shared baseline

The cross-weight issue suggests conditioning on each baseline input `S`,
not just on its cardinality. For every missing input position `p`, compare
the executions on `S` and `S+{p}`. Monotonicity and conservation imply
that they differ by one extra output one, at a unique wire. Let

```text
r_i(S) = number of missing positions p whose extra one appears at wire i.
```

Then `r_i(S)>=0`, `sum_i r_i(S)=n-|S|`, and `r_i(S)>0` only at a
zero-valued baseline output. The face matrix and its contexts factor as

```text
Q^k(i,j)   = sum_(|S|=k) r_i(S)*r_j(S),             i != j,
C^k(i,j;b)= sum_(|S|=k) r_i(S)*r_j(S)*f_b(S).
```

Each product counts the unordered missing-position pairs routed to the
two different wires. This gives a common conditional Gram representation,
rather than independently selectable pair/context entries.

For a gate with baseline bits `(f_a(S),f_b(S))`, its group update is

| Baseline bits | New group at min `a` | New group at max `b` |
|---|---|---|
| 00 | 0 | `r_a+r_b` |
| 01 | `r_a` | 0 |
| 10 | `r_b` | 0 |
| 11 | 0 | 0 |

In the last three rows, groups at occupied input wires are already zero.
All other groups are unchanged. Sorting requires, for **every baseline**
of weight `k`, that all `n-k` missing-position additions share the single
output wire `n-k-1`. This is equivalent to coalescing all its middle faces.
These identities are derived here, not formalized in this update.

### Why scalar minimum height cannot control these groups

There is an elementary obstruction even at logarithmic prefix depth.
On `n=2^h+1` wires, compute the OR of the first `2^h` inputs with a
balanced comparator tree, then compare its max output with the last input.
The min output computes

```text
F = OR(first 2^h inputs) AND last input.
```

Its scalar height is zero: the final height update takes the minimum of
`h` and zero. At the baseline with only the last input one, however,
every missing input addition changes `F` to one. Its routing group has
size `2^h`, despite `2^(scalar height)=1`.

The global minimum zero certificate has size one (the last input is zero).
At this particular baseline it has size `2^h` (all first-block inputs
must be zero). The script checks actual executions for `n=5,9,...,129`,
at prefix depths `3,4,...,8`. This separates a minimum over all inputs
from the certificate valid in the shared routing context.

More precisely, the positions in the routing group at wire `i` are the
intersection of **all zero certificates contained in the baseline's zero
support**. A missing position is pivotal exactly when every such
certificate contains it. Consequently

```text
r_i(S) <= size of a minimum zero certificate valid at S.
```

The scalar bound for a globally smallest certificate cannot replace that
conditional certificate size. See the existing
[certificate-family analysis](kahale-certificate-families.md) for the
distinction between minima, chosen witnesses, and full families.

## 4. Revised target

Degree-resolved scalar reserves do not by themselves supply the desired
local penalty. Keep the exact baseline routing groups and conditional
certificate families together, across adjacent input weights.

The next candidate should bound how quickly these groups can concentrate
for many baselines at once, using certificates valid at those same
baselines. It must account for the neighboring-weight completion horizon
above and pass the low-height OR/AND example. The group sum alone gives
only an ordinary binary-merging bound; Gram positivity alone is not being
claimed to improve the coefficient.

### The simplest conditional-certificate average also has a barrier

We additionally tested the quantity

```text
C(prefix) = sum_(all Boolean inputs x) sum_i
              minimum certificate size for the actual output value at i,
              using positions consistent with x.
```

These are exact conditional minima, not one chosen certificate and not
the minimum over all inputs. The script computes them by subset dynamic
programming and challenges every disjoint layer of the complete four- and
five-wire reachable catalogues.

| Wires | Layer queries | Largest exact growth factor |
|---:|---:|---:|
| 4 | 2349 | `51/40 = 1.275` |
| 5 | 1083425 | `59/48` |

The four-wire witness is the prefix layer `[(0,1),(2,3)]`, followed by
`[(0,2),(1,3)]`. Its cost rises from `80` to `102` when summed over all
16 inputs, disproving the candidate universal `5/4` layer-growth cap.
Parallel disjoint copies preserve the ratio: certificates for functions
supported on one block do not require positions in other blocks. Thus the
obstruction extends to arbitrarily large widths divisible by four. The
five-wire maximum is smaller because an idle fifth wire contributes to
the denominator; it does not rescue a uniform bound.

This does not rule out an amortized bound, or a potential retaining the
joint group/certificate distribution. It prevents replacing the missing
compatibility argument by an unproved bound on this simple average.

A quantitative compatibility inequality across a number of layers
proportional to `log n` is still missing. This update narrows the target and
provides explicit challenges; it does not establish a path to coefficient 4.
No additional Lean scaffold was added before such an inequality exists.

## Reproduction

```text
python -B scripts/kahale_degree_recycling.py --output docs/kahale-degree-recycling-results.json
python -B scripts/kahale_conditional_certificates.py --wires 4 --output docs/kahale-conditional-certificates-four-results.json
python -B scripts/kahale_conditional_certificates.py --wires 5 --output docs/kahale-conditional-certificates-results.json
```

The JSON contains actual comparator prefixes, exact spectral fractions,
neighboring-weight witnesses, and the logarithmic-depth conditional-height
examples. No floating eigensolver is used. No new Lean files or axioms were
introduced in this investigation.
