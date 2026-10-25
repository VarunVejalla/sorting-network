# Pair union costs: rate test (LB-24)

## Verdict

The pairwise union-cost relaxation does **not** force a rate above
`1/(1 - log2 phi) = 3.27056`. The kill test succeeds: the LB-02 barrier
schedule (skip-wide block halving), followed by two odd-even transposition
layers, meets every requirement of the pair relaxation at the Kahale witness
arity `N_d = floor(2^d/((d+1)F_{d+1}))` for every tested depth
`d = 24, 28, ..., 56, 60, 64` (exact integer computation on the full
`n x n` pair matrices, `n <= 16530`). The relaxation is also contained in
Kahale's, so its optimum satisfies `N_d <= n*_pair(d) <= U_d` on those depths.
Within the schedule family the pair matrix costs a constant factor of about 2
in the feasible `n` (about one bit), with no growth in `d`. A rate of 3.5
would need about `0.02 d` bits.

The two facts that make up the barrier:

1. **At the endpoint the pair condition is the per-wire condition.** "No
   disjoint pair `(S in Z_j, T in O_i)` with `i < j`" is equivalent to the
   per-wire thresholds `z_j >= j+1`, `o_i >= n-i`. So pairs add no
   requirement. They can only lower the upper bounds on certificate sizes
   through overlap.
2. **The defect lives where every union bound saturates.** The actual
   barrier network fails by a constant fraction of `n`: a middle wire's
   rank is off by about `0.065 n` at the end (random-permutation witness),
   and the window condition is already violated `log2 n - 4` stages before
   the end. On those middle wires the pair (and per-wire) upper bound is the
   trivial cap `n`. Overlap savings in the pair matrix peak around
   `t ~ log2 n` and then are absorbed by the cap (final saving share 0.13% at
   `d = 56`).

## 1. The pair quantity

For wires `i <= j` after `t` stages let

```text
D_ij = min{ |S| + |T| : S a zero certificate of j, T a one certificate of i,
            S ∩ T = ∅ }      (∞ if no such pair).
```

A disjoint pair is the same as a partial assignment (`S -> 0`, `T -> 1`)
forcing `out_j = 0` and `out_i = 1`. Monotonicity lets the free inputs be
anything. Sorting is `D_ij = ∞` for all `i < j`
(`sorts_iff_certificates_intersect`).

**Endpoint equivalence.** Suppose `z_j <= j` for some `j`. Take a zero
certificate `S` with `|S| <= j` and the input whose zeros are exactly `S`.
Its sorted output has a one at position `j`, but `out_j = 0`. So some `i < j`
has `out_i = 1`, and `T = complement(S)` is a one certificate of `i`
disjoint from `S`. The one side is dual. Conversely, a finite `D_ij` with
`i < j` gives an unsorted input, which violates
`sorts_iff_certificate_card_bounds`. Hence the terminal pair constraint is
exactly the per-wire threshold system. Any gain from pairs must come from
the **dynamics**: sharper upper bounds on `z` and `o`.

`D_ij` itself has no closed sum-type upper recurrence. Combining two
restrictions needs their supports to be compatible (no input set to both 0
and 1), and that is not a function of their sizes. The closed object is
therefore the single-polarity union-cost matrix of
`PairUnionRecurrence.lean`:

- `Z_xy`: the minimum size of a set forcing both `x` and `y` to zero;
- `O_xy`: the dual for ones;
- `Z_xx = z_x`.

The script uses exact sizes, not heights. It applies the recurrence to a
whole layer of disjoint comparators. On the zero side a min output is
`OR(a, b)` and a max output is `AND(a, b)`; on the one side the roles swap.

| Output pair | Bound |
|---|---|
| OR, OR | `min over u in {x, px}, v in {y, py}` of `Z_uv` (exact) |
| AND, OR | `min over v` of `T(x, px, v)`, with `T(a, b, v) = min(Z_ab + z_v, Z_av + z_b, Z_bv + z_a)` |
| AND, AND | `min(Z_{x px} + Z_{y py}, Z_xy + Z_{px py}, Z_{x py} + Z_{px y})` |
| gate pair | `Z_{x px}` |

After each layer the script also:

- caps every entry at `n`;
- imposes `Z_xy <= z_x + z_y`;
- tightens `z_x <= min_y Z_xy`.

Each rule is a certificate union or a family identity. The pairing rule
dominates the sequential pair-plus-single covers of `kahale-weighted-union.md`.
Soundness was tested against exact certificate minima (all `2^n` inputs) on
90 random layered networks with 6, 8 and 10 wires, 8 layers each. Every entry
was a valid upper bound, about 46% of entries were exact, and the per-wire
gain reached 4.

**Requirements**, with `s` stages remaining:

- `(GZ)` `z_i >= i - 2^s + 1` and `(GO)` `o_i >= n - i - 2^s`. These are the
  sized forms of LB-02's graded (G), from the rank window `[i-2^s, i+2^s]`.
- At `s = 0`, the exact thresholds `z_i >= i+1` and `o_i >= n-i`.
- `(W)`: every comparator has `j - i <= 2^(s'+1) - 1`. The schedule
  satisfies this by construction.

The sized requirements imply Kahale's height condition (Z). The pair values
satisfy pair `<=` per-wire sizes `<= 2^height`. So every pair-feasible
schedule is feasible for Kahale's system, and `n*_pair(d) <= U_d =
min_s 2^(d+1)(s+1)/C(d-s,s)`, the kernel-checked bound.

## 2. Kill test at `N_d`

The schedule is the skip-wide block halving of LB-02 (widths legal for total
depth `d+2`), followed by 2 odd-even transposition layers. Total depth
`d+2` does not change the rate.

`n/a` means the heights model was not run at that depth; LB-02 already
checked it to `d = 1024`.

| `d` | `N_d` | `d/log2 N_d` | heights | wire sizes | pair matrix | pair interior min slack |
|---:|---:|---:|:-:|:-:|:-:|---:|
| 24 | 8 | 8.00 | ok | ok | ok | 2 |
| 28 | 18 | 6.71 | ok | ok | ok | 2 |
| 32 | 36 | 6.19 | ok | ok | ok | 1 |
| 36 | 76 | 5.76 | ok | ok | ok | 1 |
| 40 | 161 | 5.46 | ok | ok | ok | 2 |
| 44 | 344 | 5.22 | ok | ok | ok | 1 |
| 48 | 738 | 5.04 | ok | ok | ok | 1 |
| 52 | 1593 | 4.89 | ok | ok | ok | 2 |
| 56 | 3459 | 4.76 | ok | ok | ok | 2 |
| 60 | 7545 | 4.66 | n/a | ok | ok | 2 |
| 64 | 16530 | 4.57 | n/a | ok | ok | 1 |

Without the 2 cleanup layers the pair model fails by exactly 1 at the
terminal step, on the third-from-top wire's one side (`o_{n-3} = 2 < 3`), for
every `d >= 30` tested. This is a genuine non-sorting defect of the plain
schedule, caused by its imperfect self-duality. One cleanup layer suffices
at `d = 40`; two suffice everywhere tested. Interior requirements (`s >= 1`)
pass with or without cleanup.

## 3. Optimisation over schedules

**Exact optimum, tiny `n`.** A breadth-first search covered all width-legal
layer schedules: every partial matching, min at the lower wire, on states
`(Z, O)` or `(z, o)`. Its minimum depth for `n = 3, 4, 5, 6` is
`3, 3, 5, 5` for both the per-wire sized and the pair relaxation. That equals
the true `D(n)`. Both relaxations are tight at these sizes, so small `n`
cannot separate them. This is an exact optimum of the relaxation.

**Heuristic family, moderate `n`.** For the barrier schedule (plus 2 cleanup
layers), the table gives the largest `n` on the grid `2^(k/8)` passing each
model. The search stops after 6 consecutive failures above the best value,
since feasibility is not monotone in `n`.

| `d` | `N_d` | heights | wire sizes | pair matrix | `log2(wire/pair)` |
|---:|---:|---:|---:|---:|---:|
| 20 | 4 | 279 | 54 | 29 | 0.90 |
| 24 | 8 | 664 | 609 | 279 | 1.13 |
| 28 | 18 | 1722 | 1448 | 664 | 1.12 |
| 32 | 36 | 4096 | 4096 | 2048 | 1.00 |
| 36 | 76 | 9742 | 8192 | 4467 | 0.87 |

The pair loss is about one bit (0.90, 1.13, 1.12, 1.00, 0.87) and does not
grow. A 3.5 rate requires the
best schedule to lose `~0.020 d` bits, which is 0.5 bits at `d = 24` and 0.7
at `d = 36`. That is the same order as the observed constant. So the scan
alone cannot rule out a slope. The decisive evidence is the kill test at
`N_d`, together with how the savings are distributed.

**Where the savings are.** The table below gives the pair-matrix savings
`sum (z_wire - z_pair) / sum z_wire` along the schedule at `N_d`.

| `d` | peak (around `t ~ log2 n`) | final |
|---:|---:|---:|
| 40 | 0.31 | 0.017 |
| 48 | 0.26 | 0.0049 |
| 56 | 0.33 | 0.0013 |

The number of entries with `Z_xy < min(n, z_x + z_y)` peaks at about `n/2`
per wire near `t = log2 n`. It falls to about 0.1 per wire in the last
`log2 n` stages, because wires reach the cap `n`. Savings are confined to
the early saturation phase, which no requirement constrains. The final
share halves every 4 stages of `d`, so it vanishes rather than compounding.

## 4. Why the pair potential cannot see the defect

The actual barrier network was run on random permutations
(`truth` mode). These samples give witnessed lower bounds on the defect.

| `d` | `n` | first witnessed window violation (`s`) | terminal rank error | worst wires |
|---:|---:|---:|---:|---|
| 32 | 36 | 1 (log2 n = 5.2) | 2 (0.056 n) | zero side 17 (rank 16), one side 26 (rank 28) |
| 40 | 161 | 3 (log2 n = 7.3) | 11 (0.068 n) | zero side 85 (rank 75), one side 74 (rank 85) |
| 48 | 738 | 5 (log2 n = 9.5) | 51 (0.069 n) | zero side 401 (rank 350), one side 424 (rank 473) |
| 56 | 3459 | 7 (log2 n = 11.8) | 240 (0.069 n) | zero side 1853 (rank 1613), one side 1542 (rank 1769) |
| 64 | 16530 | 10 (log2 n = 14.0) | 1075 (0.065 n) | zero side 8725 (rank 7650), one side 7510 (rank 8572) |

The worst wires are in the middle. For example, at `d = 48` wire 401 holds
rank 350, so its true zero size is `<= 351` against a requirement of 402.
At `d = 40` wire 85 has true `z <= 76` against 86, the analogue of the
161-wire defect (77 vs 87 on wires 85/86). For the worst wires of a
separate 4096-sample run, the pair model and the per-wire model both give
`z = n`: the union bound has hit the cap. Those wires are 91 at `d = 40`
(true `z <= 81`) and 359 at `d = 48` (true `z <= 310`). Hence:

- **Saturation.** In the middle, certificates have size `~n/2`. Any two of
  them overlap in `~n/4` inputs, and the true `Z_ab` is close to
  `max(z_a, z_b)`. A closed bound built from sums (`Z + z`) exceeds `n` after
  a few AND steps and is then capped. A pair matrix stores one overlap per
  pair. It charges the third and later certificates in a union as disjoint,
  and that is exactly where the middle-wire reconvergence lives.
- **Polarity separation.** `Z` and `O` evolve independently. The defect is
  mixed-polarity: a zero certificate and a one certificate that are
  disjoint. The only cross-polarity input is the coupling `z + o <= n + 2`,
  which LB-02 showed never binds.
- **Kahale's count binds at the edges.** It concerns the top and bottom
  `2^(s+1)` wires with small certificates, where overlaps are rare (the
  low-height classes are tree-like). The pair matrix is accurate there and
  agrees with per-wire sizes.

**Remark (observation, not used).** The constant is algebraically Valiant's
amplification exponent. For `A(p) = 1 - (1-p^2)^2`, the fixed point is
`p* = 1/phi` and `A'(p*) = 4/phi^2`. Two layers per application give depth
`2 log2 n / log2(4/phi^2) = log2 n / (1 - log2 phi)`. Boppana (1989; recalled
from memory, check before citing) showed read-once amplifiers cannot do
better. This suggests that 3.2706 is the "tree-like / independent
certificates" barrier. Every relaxation that is satisfied when the
certificates of compared wires behave independently stops there. That
includes per-wire heights, two-sided heights and pair union costs.

## 5. What a rate above 3.2706 would need

No better rate appeared, so there is no theorem to state for the pair
relaxation. A rate-bearing cross-wire structure must:

- (a) stay informative on middle wires at size `~n/2` (not saturate);
- (b) couple polarities;
- (c) charge reconvergence of three or more certificates.

Recommended next structure, in order:

1. **Mixed-polarity restriction families.** For wire pairs `i < j`, track
   partial assignments forcing `(out_i, out_j) = (1, 0)`, kept with their
   supports (or support profiles by position class), so that compatibility
   is decidable. A rate statement would bound how many such restrictions one
   layer can kill in the last `~log2 n` stages. The witness to explain is
   the middle-wire defect above (`~0.065 n` rank error, which enters at
   `s ~ log2 n - 4`).
2. **Correlation or probability potentials** in Bernoulli or random
   permutations. Under the van den Berg–Kesten / Reimer inequality,
   `P(A □ B) <= P(A) P(B)` charges disjoint occurrence against the
   overlapping occurrence `P(A ∩ B)`. This is the non-read-once correction
   that the Valiant/Boppana remark points to. It is natural on the middle
   wires.
3. Plain `k`-wise union costs. These are not recommended: they cost `n^k`
   and saturate in the same way.

## Reproduce

Run from the repository root.

```sh
S=lower-bound/experiments/scripts/kahale_pair_union_rate.py
python -B $S validate 6 8 10 --depth 8
python -B $S run 24 28 32 36 40 44 48 52 56 --cleanup 2 --stats
python -B $S run 60 64 --cleanup 2 --models wire,pair      # ~1 h, 2.5 GB at d=64
python -B $S run 32 40 --cleanup 0                          # terminal -1 defect
python -B $S scan 20 24 28 32 36 --models pair --cleanup 2 --nmax 12000
python -B $S scan 20 24 28 32 36 40 44 48 52 56 --models heights,wire --cleanup 2 --nmax 2000000
python -B $S exact 3 4 5 6 --depth 8                        # ~11 min
python -B $S truth 32 40 48 56 64 --cleanup 2 --samples 1024
```

Outputs: [`kahale-pair-union-rate-output.txt`](kahale-pair-union-rate-output.txt).
These are exact finite computations of a relaxation, plus sampled runs of
the actual network. They make no sorting claim and add no Lean.
