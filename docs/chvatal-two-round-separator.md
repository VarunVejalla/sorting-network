# Two-round separator: bulk lemma and fringe bottleneck

Research analysis, 2026-10-10. These arguments are derived and unaudited, not
Lean-checked. No new sorting-depth theorem is claimed. Companion analysis:
[separator requirements and costs](chvatal-separator-cost-analysis.md).

**Follow-up correction:** [a stronger adversary](chvatal-fringe-obstruction.md)
rules out establishing today's F contract in the first scramble at the proposed
smaller fringe size. The conditional bulk calculation remains useful, but F
must instead be established across both rounds or the scheduler must change.

## 1. Bulk contraction with a simultaneous witness

Fix matrix dimensions `m,n`, with `n >= 16`. Choose a first scramble satisfying
the existing universal bulk guarantee at error
`e = sqrt(2*(1+ln m)/m)`. The existing union bound supplies this with failure
probability below 1/100 when `m >= 100`.

For a threshold selecting exactly `i*n` largest keys, the sorted intermediate
column heights `s_c` have mean exactly `i`. Its first-round bulk guarantee gives

`L = (1/n)*sum_c |s_c-i| = (2/n)*sum_c (s_c-i)_+ <= e*m`.

Exact mass is essential to this displayed identity. The old combinatorial
interface allows total mass less than `i*n`; the new argument can instead use
the exact-mass semantic interface directly.

Choose an independent second scramble. For any subset `S` of `s` columns, let
`Y` count threshold marks sent into it. Each row contributes a hypergeometric
count, and rows are independent. Its moment-generating function is bounded by
that of independent Bernoulli cells with the same row marginals (this comparison
is an explicit proof obligation). The resulting Bernstein variance proxy is

`s*V`, where `V = sum_r p_r*(1-p_r)
 = (1/(2*n^2))*sum_{c,d}|s_c-s_d| <= L <= e*m`.

The cell-level mgf comparison is crucial: applying a bounded-increment inequality
to entire rows, with increment bound `s`, loses the useful rate.

If final excess above `i` is at least `d*m*n/2`, its positive-excess columns
provide a subset `S` with `Y-s*i >= d*m*n/2`. Bernstein therefore gives

`P[bad for this state and S] <= exp(-n*I)`,
`I = d^2*m/(8*e + 4*d/3)`.

Union over at most `(m+1)^n` intermediate height vectors, `2^n` subsets, and
`m` thresholds. Thus a conservative one-sided failure bound is

`m*exp(n*(ln(2*(m+1))-I))`.

Including both orientations, a sufficient condition for second-round failure
less than 1/100, uniformly for `n >= 16`, is

`I > ln(2*(m+1)) + ln(200*m)/16`.

This chooses one second scramble working for every admissible intermediate
state; there is no exchange of the fixed-input and all-input quantifiers.
At `m=2^42`, `d=1/59000000`, floating-point evaluation gives `e≈3.70046e-6`,
`I≈42.646`, and the required right side approximately `31.956`. These are
exploratory numerics; rigorous logarithm bounds remain an obligation. The first
scramble must also meet a separately proved fringe guarantee at these dimensions.

## 2. Fringe preservation is deterministic

For any key threshold, a row scramble preserves the number of marked keys in
every row prefix and suffix. Ascending column sorting moves high-key marks
downward, so their count in any top row prefix cannot increase. Low-key marks
in any bottom row suffix likewise cannot increase.

Consequently, appending a row scramble and column sort preserves every existing
Property F inequality, for both orientations and every supported rank `j`.
It also preserves Property B at row-aligned cuts. Physical packs require tracking
the cumulative row-preserving relabeling; these permutations preserve the same
region counts and comparator orientation. Arbitrary cuts inside rows are not
covered by this argument.

There is no need to re-prove F probabilistically for the second scramble.
There is a need to establish F for the first scramble at smaller dimensions.

## 3. Why the current fringe proof blocks the numerical candidate

`NodeGeom` scales templates with a fringe ratio as small as
`f/m = 4095/2^37` (approximately `2.98e-8`). At `m≈2^42`, such templates
have only about 131040 fringe rows. The existing F existence theorem demands
`f >= 8500000000`. For a template with the displayed ratio, this alone requires
`m >= 8500000000*2^37/4095`, essentially the existing `2^58` scale.

Therefore retaining that sufficient condition makes two rounds more expensive,
not an improvement. The earlier cost sketches that used only `m >= 2*f` omitted
this much smaller scheduler-specific fringe ratio.

An identifiable source of the large threshold is `Lemma62Round.round_event`:
it rounds rank `j` up to `j' = 86000000*ceil(j/86000000)`, then requires
`j' <= f*n/31`. For small `j`, this can inflate the rank dramatically.
Several numeric lemmas also use the loose bound
`-ln(epsF) <= 86000000`; improving that estimate alone does not repair the
rounding step or its small-rank assumptions.

## 4. Construction and honest cost

Use column sort, first scramble, column sort, second scramble, column sort.
The intermediate sort is shared: total depth at most `3*S(m)`, not `4*S(m)`.
For `m <= 2^k`, bitonic `S(m) <= k*(k+1)/2`; with the present scheduler,
the asymptotic coefficient is at most `3*k*(k+1)/4`.

For exactly `m=2^42`, this gives 1354.5. The actual templates are not generally
powers of two: rescaling into `2^42 < m <= 2^43` would cost at most 1419,
provided the bulk bounds, fringe existence, scaling, and small-node handling
are all proved for that range. The current fallback for small nodes also needs
a reduced threshold to fit this new budget; its depth must not be overlooked.

More full-sort rounds are not automatically cheaper. Using the conservative
Bernstein recurrence and the same union-bound margin, exploratory powers of
two give (scrambles, k, coefficient): `(2,42,1354.5)`, `(3,38,1482)`,
`(4,36,1665)`. These omit geometry and fringe restrictions and are not theorems.

## 5. Next modular obligations

1. Prove deterministic row-cut monotonicity and cumulative relabeling invariants.
2. Prove the finite hypergeometric mgf comparison and Bernstein bound, then the
   restricted-state universal second-scramble lemma at exact mass.
3. Replace the F rounding argument: handle rare ranks directly when the required
   miss count is zero, and use a separate relative-error argument for larger
   ranks. Determine whether `f≈2^17` is sufficient before formalizing numbers.
4. Only after F is feasible, redo template scaling and small-node cutoffs,
   preserving the scheduler's four-field NodeSpec interface.

Priority: the smaller-fringe existence lemma. The bulk candidate now has a
concrete concentration route, but cannot improve the sorter without that lemma.
Cheap repair remains a later option for pushing below the full-sort budget.
