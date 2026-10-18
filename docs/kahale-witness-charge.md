# Amortized witness charges: an additive barrier and a nonlinear escape

## Status

This follows [shared comparator polarity](kahale-joint-polarity.md).
We have now tested actual amortized inequalities, rather than only exact
transport. All results below are finite-width, exact-arithmetic Python
certificates or derived arguments. They are not Lean checked and do not
improve the universal coefficient 3.270559454.

The main result is a distinction between two kinds of compatibility:

- **Within one input:** a mixed witness requests several ones and zeros
  in the same image point.
- **Across the image:** different witness obligations remain present,
  possibly on different inputs, and one suffix must handle them all.

Even all orders of the first kind, with signed additive charges, fail on
the small benchmark. Signed quadratic charges of the second kind escape
that barrier and recover the exact four- and five-wire sorting depths.
The missing asymptotic step is a scale-compatible version of this
nonlinear charge.

## 1. A concrete amortized inequality to test

For a mixed pattern `p=(k,A,B)`, let `F_p(R)` indicate that some point
of image `R` has weight `k`, ones on `A`, and zeros on `B`. Retain only
**bad** patterns: a forced one lies before a forced zero. Every such
feature vanishes on the sorted image.

For fixed coefficients, define

```text
Phi(R) = sum_p w_p F_p(R).
```

Impose, for every actual reachable image and every parallel layer,

```text
Phi(R) - Phi(L(R)) <= 1.
```

Then every full sorter has depth at least `Phi(full cube)`, by telescoping
to terminal value zero. The potential may increase on a layer, and signed
weights or negative intermediate values do not invalidate the argument.

The script enumerates all images and layers through five wires, forms
these inequalities, and maximizes the initial potential. It separately
tests witness existence and the number of **distinct image points**
witnessing a pattern; the latter is not input multiplicity.

LP output is converted to rational coefficients and every layer inequality
is checked using exact fractions. Matching rational dual certificates
prove the reported optima within the specified families. For nonnegative
weights the dual weighted sum must dominate each initial feature; for
free signed weights it must equal it. The saved results include both
primal coefficients and dual layer weights.

## 2. Exact finite limits of additive witness charges

| Wires | Additive feature family | Nonnegative optimum | Signed optimum | True depth |
| ---: | :--- | ---: | ---: | ---: |
| 4 | Pair inversion witnesses | 2 | 2 | 3 |
| 4 | All mixed witness orders | 2 | 2 | 3 |
| 5 | Pair inversion witnesses | 3 | 3 | 5 |
| 5 | Mixed orders up to 4 | 143/47 | 13/4 | 5 |
| 5 | All mixed witness orders | 143/47 | 13/4 | 5 |

All optima in this table have exact matching primal and dual certificates.
On five wires, raw witness counts reach only 2 with nonnegative weights
and 7/3 with signed weights, even at full order. Merely growing witness
arity or allowing signed additive corrections is therefore insufficient
to recover the finite benchmark.

This is a limitation of these finite charge families, not a theorem
excluding all asymptotic witness methods.

### A two-line dual proof of the four-wire barrier

Let `R0` be the full four-wire cube, and define the actual images

```text
R1 = [(0,3),(1,2)](R0)
R2 = [(0,3)](R0)
R3 = [(0,1),(2,3)](R2).
```

Ignoring the sorted points, which witness no bad pattern, their points are

| Rank | R1 | R3 |
| ---: | :--- | :--- |
| 1 | 4 | 2 |
| 2 | 6, 9 | 10 |
| 3 | 13 | 11 |

Here integer masks use bit `i` for wire `i`. The unsorted points of `R2`
are exactly the disjoint union of these two columns. At each rank, the
two columns also have disjoint sets of inversion pairs. A bad mixed
pattern contains an inversion pair, so it cannot be witnessed in both
columns at the same rank. Thus, for every bad mixed witness of any arity,

```text
F_p(R2) = F_p(R1) + F_p(R3).
```

The same identity holds for raw distinct-point counts by disjointness.
It holds for any signed linear combination of those features. Its
one-layer inequalities on `R0 -> R1` and `R2 -> R3` imply

```text
Phi(R0) - Phi(R1) <= 1,
Phi(R2) - Phi(R3) = Phi(R1) <= 1,
therefore Phi(R0) <= 2.
```

This explains the barrier without relying on numerical optimization.
There is no actual two-layer four-wire sorter. The additive functional
combines progress from different residual branches as if their charges
belonged to one compatible schedule. Full witness order does not fix
that accounting mistake.

## 3. The nonlinear escape: simultaneous obligations

Start with rank-specific pair inversion predicates `F_p`, and include
products

```text
F_p(R) F_q(R), with |rank(p)-rank(q)| <= 1.
```

This product means that both obligations are present in the image.
Their witnesses may be different inputs. It does **not** assert that
one input satisfies both bit patterns, nor that two witnesses differ
by a single coordinate. That is precisely the distinction from enlarging
the within-input mixed pattern.

Use a signed quadratic potential with the same one-layer decrement cap.
Identical feature columns on the complete finite catalogue are merged
for the optimization; this is only a finite computational simplification.

| Wires | Distinct quadratic features | Nonnegative optimum | Signed optimum |
| ---: | ---: | ---: | ---: |
| 4 | 59 | 2 | 3 |
| 5 | 294 | 251/82 | 1287/290 |

All four optima have exactly verified rational primal and dual certificates.
The signed potentials start at 3 and approximately 4.43793 respectively,
vanish on the sorted image, and lose at most one on every actual layer.
Since depth is integral, they prove finite lower bounds 3 and 5, matching
the exact benchmark. **4.43793 is a potential value at five wires, not
an asymptotic coefficient.**

The optimal signed formulas have 21 and 217 active terms respectively.
The five-wire formula is too dense to regard as an explanatory research
invariant. An additional L1 minimization seeks simpler valid certificates
at initial values 3 and 41/10; its rationalized coefficients and exact
checks are saved separately. L1 minimization encourages small coefficients
but does not prove a minimum number of terms.

The simplification gives 10 terms on four wires with value exactly 3,
and 78 on five wires with value `68333/16667 > 4`. The latter still
certifies depth five after rational rounding and rescaling; it remains
too large to call a simple structural formula.

### An explicit four-wire nonlinear potential

Write `I^k_ab` for the indicator that an image point of weight `k` has
an inversion at wires `a<b`. The simplified formula is

```text
3 Phi = I^2_01 I^2_02 + I^3_02 I^3_03 + I^2_03 I^2_12
      + I^1_12 - I^1_12 I^1_23
      + 3 I^2_12 - I^2_12 I^2_13 - I^2_12 I^1_23
      + 2 I^2_13 + 3 I^1_23.
```

It starts at 3, ends at zero, and loses at most one on all 396 actual
image/layer transitions. The negative cross terms account for overlap
between simultaneous tasks; they are not counts of individual input
patterns. This is an explicit finite invariant with an exhaustive exact
check, not yet an all-size inequality or a kernel-checked theorem.

## 4. Why image realizability must survive the abstraction

The formula above is not valid on every arbitrary Boolean domain. For

```text
R = {0,2,3,7,8,9,11,12,14,15},
L = [(0,2),(1,3)],
```

its decrement is `8/3`, exceeding one. This domain contains all sorted
points, has predecessors and successors at consecutive ranks for every
nonterminal point, and has connected rank slices under one-bit exchanges.
The script checks these properties and the violated charge exactly.
Those simple consistency conditions therefore do not justify lifting
the fitted potential to arbitrary projected domains.

There is a short reason why `R` cannot be the image of any monotone
weight-preserving map of the four-cube. Its rank-one points are masks
`2` and `8`. Every input singleton must map to one of those two colors.
To produce rank-two point `3`, both singleton inputs of a preimage must
have color `2`; at least two input singletons need that color.
To produce the distinct rank-two points `9` and `12`, their preimages
must be distinct pairs of singleton inputs all colored `8`. At least
three inputs need color `8`, since two inputs give only one pair.
Thus at least `2+3=5` input singletons would be needed, contradicting four.
This is a derived counting proof independent of solver UNSAT reports.

More generally, if `F` is monotone and weight-preserving, write `q(i)`
for the output coordinate of input singleton `i`. Every preimage `S` of
an output set `y` satisfies `q(S) subset y`. Distinct image points require
distinct preimages. Consequently, for each collection `T` of rank-`k`
image points,

```text
|T| <= |{ S : |S|=k, q(S) subset y for some y in T }|.
```

This is a preimage-capacity/Hall constraint, derived by choosing one
preimage of each output point. It is related to the earlier routing-group
and Hall investigations, rather than a claim of a new published result.
At a nonempty baseline, the same argument uses its singleton-addition
routing groups and the monotone, conserving map on that upward subcube.
Compatibility between these baseline constraints remains part of the
missing multiscale argument.

## 5. What this suggests, and what still must be proved

The successful finite charge depends on overlapping **remaining tasks**,
not only on how many mixed patterns one layer resolves. A general
potential should retain a nonlinear interaction between witness families
on neighboring ranks. The coefficients must come from an understandable
rule in ranks, wire positions, or separator structure; a fitted table
for one width is not a universal inequality.

Replicating the finite gadgets does not supply the missing logarithm.
For independent blocks, summing a local potential gives decrement at
most the number of blocks, since every block can make progress in one
parallel layer. Averaging restores unit decrement but keeps the initial
value constant. This is an analytic replication check, not a tested
multiscale construction.

The next concrete target is therefore a **scale-compatible nonlinear
interaction term**, preserving the preimage capacities that exclude
unrealizable domains. The four-wire formula now exposes explicit overlap
corrections. Next test whether a
nested version gives growing initial value while keeping the global
per-layer decrement controlled. A layer may advance several levels
concurrently, so adding the same finite correction at every level would
need proof. The efficient recursive prefixes, sorted-block/mirror
preparation, and small optimal sorters must remain counterexample tests.

No bound above 3.270559454 follows yet. No asymptotic coefficient is
forecast from these finite optima.

## Reproduction and checks

```text
python -B lower-bound/experiments/scripts/kahale_witness_charge.py --output docs/kahale-witness-charge-results.json
```

SciPy computes candidate coefficients; exact `Fraction` arithmetic checks
them and their dual certificates. There are 396 layer inequalities on
four wires and 14,525 on five. The checks cover the complete actual
image catalogues, not samples. This remains Python verification rather
than Lean kernel checking. No Lean files, builds, or dependencies were
added. Long output is kept in the gitignored `LLM-helpers` log.
# Follow-up: singleton capacities

The [preimage-capacity screen](kahale-preimage-capacity.md) extends the
four-wire ten-term inequality to all 101 domains satisfying independent-rank
bottom singleton capacities, with 909 exact layer checks. No scale lift or
asymptotic improvement is established.

