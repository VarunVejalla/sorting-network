# Algorithm research toward 700 and 200

Audit date: 2026-10-13. This is a research agenda, not a new sorting bound.
The accepted endpoint remains 1419. The tapered worktree is developing 945;
its local separator providers and conditional transition lemmas are much
further along than the old backlog suggests, but its global scheduler,
outsider induction, terminal construction, and endpoint audit remain open.
Source inspection here did not rebuild or independently verify Lean results.

## 1. Use the actual repeated cost

The best package's `AKS/Chvatal/PhysicalPack2.lean` and `SeparatorDepth.lean`
charge three full column sorts. The current tapered
`AdaptivePaddedWitness.lean` gives one actual network of depth at most 1890,
with arbitrary-cut crossing bounds and both rare-rank bounds. Its large-size
branch uses rows between `2^34` and `2^35`; its small branch uses width 16.
The triangular sorter budget is `S(q)=q(q+1)/2`, so `S(35)=630`.

The intended tapered schedule has three ordinary nodes per six input bits.
If that complete schedule closes, its coefficient is `T/2`, where `T` is the
uniform node depth. Thus retaining the first two full sorts gives:

| Final operation, including repair | Node depth | Conditional coefficient |
| ---: | ---: | ---: |
| 630 | 1890 | 945 |
| 400 | 1660 | 830 |
| 300 | 1560 | 780 |
| 200 | 1460 | 730 |
| 140 | 1400 | 700 |
| 136 | 1396 | 698 |

These are budget calculations, not candidate constructions. In particular,
`S(16)=136` does not mean that a 136-layer repair exists. Every serial fringe
operation must be included; only operations on disjoint wires can share depth.
A reparameterized schedule must recompute its stages per bit.

Keeping two depth-630 sorts gives a coefficient floor of 630 in this frozen
accounting. Keeping even one gives 315. Reaching 200 therefore requires
changing those full sorts or changing the schedule, even with free cleanup.

## 2. First bet for 700: replace the last sort, with a precise promise

Rebase UB-14 on the tapered contract. Its old projected 1050 concerned the
1419 schedule. A 200-layer final operation would instead price to 730 under
the intended tapered accounting. It is useful progress, but does not reach
700; the complete final-operation gate is 140 layers.

The right first theorem compares a specified repair with the full final sort
at each required cut. For a Boolean column with total high-key mass `s`, a
band straddling row cut `i`, high-key mass `U` above the band's upper edge,
and low-key mass `D` below its lower edge, sorting that band gives

```text
wrong_high_after_band <= (s - (m-i))_+ + U + D.
```

Here row indices increase downward; the first term is the full-column-sort
baseline. Equivalent height-oriented notation is in
`experiments/global-cost-audit/central-bulk-feasibility.md`, section 3.
Sum this inequality over columns, reserve `U+D` inside the bulk budget, and
price the band sorter. A comparison with the matrix's total mass alone is
invalid: a column-local repair cannot transfer capacity between columns.

Required order of work:

1. Specify the actual comparator network, the cuts it repairs, the tail
   functional it needs, and its depth. Prove the deterministic cut inequality.
2. Prove that one fixed pair of scrambles supplies this tail promise for every
   admissible input, all required ranks/cuts, and both orientations. The input
   may be chosen after the scrambles. Include padding and joint failure costs.
3. Preserve the multiplicative rare-rank guarantee of the same network.
   Monotonicity of a partial repair does not supply the contraction proved
   using a full final sort.
4. Install the provider into the actual flow and price the complete recurrence.

This path is my first choice for a focused local experiment. Its 140-layer
target is demanding; I do not currently have a uniform tail proof that makes
698 a credible certified projection.

### Why typical displacement and the old L1 bound do not suffice

There is a concrete obstruction in the enlarged L1 profile class. Take
`m=2^34`, cut `i=m/2`, and `v=m/4`. Put a fraction `alpha=2*E1` of column
heights at each of `i-v` and `i+v`, and the rest at `i`, with
`E1=38/10^6`. Choose the number of columns to make these counts integral.
The mean height is `i`, and the mean absolute deviation is exactly `E1*m`.
For a band half-width `W <= v/2`, the high-key mass outside the band is at
least `E1*m*n/4`, approximately `163209*n`. The tapered per-cut allowance
`2^-21*m*n/2` is only `4096*n`, about 40 times smaller. A row scramble
preserves the mass in this outside region, and a repair confined to the band
cannot remove it.

This is a hand-derived counterexample to obtaining a narrow-band promise from
L1 control alone. It is not a proof that the profile is reachable after a
selected first scramble. Excluding it uniformly is the missing extra theorem.
RMS displacement or sampled maximum displacement does not exclude it.

Nor does deleting layers from a full sorter immediately produce the cheap
desired primitive. Saving a few terminal layers is a different operation from
proving that a promised input can be repaired by sorting a short interval.
Name and prove the latter network rather than infer its cost from `S(log d)`.

## 3. Simplify the provider seam before adding a construction

UB-18 is a short interface audit. The current tapered
`AdaptivePaddedWitness.crossing` quantifies over **every** wire cut `r <= a`.
That is stronger than the old fixed 65-cut table. A gadget passing only those
65 cuts does not implement the tapered interface.

List the cuts actually consumed by `badSend0`, `fringeSend`, and each moving
frontier. Separate positional output cuts, native rank thresholds, and their
input-tail premises. A bag's output port sizes are fixed by its schedule, so
it may be possible to require just the prescribed cuts while retaining every
input/rank quantifier. Prove that restricted interface sufficient before
searching only at those cuts. Frontier cuts must be included. This is an open
simplification lead, not an assertion that arbitrary-cut control is dispensable.

For exact column sorters, UB-01 can package generic sortedness, permutation
and column-count preservation, fixed behavior on sorted columns, ordered
comparator endpoints, and depth. `MatrixBridge`, `Bulk2Bridge`, `FlipSpec`,
and `PhysicalPack2` are the source seams. `FlipSpec` uses sortedness and
permutation facts rather than an apparent bitonic-specific identity.
Keep exact sorting and promised repair as distinct contracts: intermediate
rounds currently consume exactly monotone columns.

The width-16 branch now uses `f=16000` and rare-rank coefficient `1/9000000`.
`CyclicSmallF2Params.lean` also shows its large-rank R2n range is empty.
This does not prove the same small fringe works at arbitrary width. UB-15
should first audit the nonempty R2n event at large widths, rather than
re-derive the already present small-width result.

Low-cost exact-sorter substitutions are useful only if they change depth.
Odd-even mergesort has the same triangular depth budget at powers of two.
Using a better small base sorter saves a fixed amount from each repeated
column sort, and hence gives a real but usually small coefficient gain.
Neither is currently a structural path to 700.

UB-13 can still help a near miss: if a compatible run-aware first sort saves
`Delta` layers, the final-repair budget becomes `140+Delta`. But the two
optimizations cannot simply be added. The existing run-aware proof uses
exactly sorted output-column runs from the previous separator; an approximate
final repair may destroy that promise. Ragged flows also need a new chunk
alignment/divisibility argument. Require a joint preserved-chunk contract
before counting both savings.

## 4. First bet for 200: change the transfer and the repair channel

Continue UB-11's ordered-window audit. The one-sided-outsider example in
`experiments/direct-multiway/TRANSFER-AUDIT.md` creates about 32 address
mismatches per parent outsider across 64 child windows. Disjoint output sets
do not justify charging that outsider once. Merely renaming the scalar
potential cannot remove these actual mismatches.

UB-19 proposes a more informative state:

* the signed cumulative discrepancy at every child cut;
* the child-count defect vector and separate left/right parent outsider mass;
* higher-order outsider counts and a distance-sensitive leakage profile.

For ordered child intervals, total window mismatch is controlled by the sum
of absolute cumulative cut displacements, with endpoint/fringe terms. Derive
the precise finite inequality before selecting weights. This resembles a
one-dimensional transport cost; it retains information lost in the current
per-child upper bound. A successful proof still has to bound that cost,
including the 32-fold example. It must close fresh forcing, initialization,
frontiers, and terminal integer purity as well as contraction.

The new construction question, UB-20, is whether adjacent child regions can
repair nearby mistakes directly instead of returning every mistake through
the parent fringe. The old flow audit's exit-bandwidth obstruction assumes
that up-flow is the repair channel. Adding a lateral comparison channel
changes that assumption and could reduce the need for extraordinarily tiny
local bulk error.

A concrete experimental family is a multiway approximate partition followed
by fixed comparisons on disjoint adjacent pairs (even boundaries, then odd
boundaries), with sparse compaction/attenuation inside the relevant regions.
The same layers must control every threshold input and both orientations.
Prove or refute a full transfer bound for this family, including far-jump
errors, retained good keys, capacity conservation, and fringe ranks. Simply
asserting that errors are adjacent is insufficient: the old locality notes
do not prove a per-key adjacent-error property against an adaptive adversary.

Goodrich's [attenuator definition](https://arxiv.org/pdf/1403.2777), section 2,
is useful as a local contract: it reduces the existing misplacement count by
a factor, rather than charging a fresh fraction of all inputs. His whole
Zig-zag Sort is not a logarithmic-depth substitute; the paper expressly
distinguishes its size result from parallel depth. A borrowed recursive
attenuator also needs its actual depth charged, not just its comparison count.

Do not use an input-dependent matching or compaction permutation as the repair
network. The existing 17-layer matching-capacity diagnostic is a useful
warning: capacity under a matching chosen for each input can be far better
than execution by the fixed comparator order. Finite search should target a
certificate for the complete simultaneous contract, not an iid objective.

For a genuinely new factor-64 macro-stage, **all** its serial operations may
total at most 4200 layers for 700, or 1200 for 200. For the existing schedule,
which consumes three nodes per factor 64, those node budgets are 1400 and 400.
They are different acceptance tests. Include arbitrary-n restriction/padding:
a bound only on a sparse size subsequence is insufficient for limsup.

## 5. Correct the literature queue

UB-09's proposed `M=16,32` extraction cannot instantiate the cited proof.
Chvatal's [Theorem 1.2 proof](https://users.encs.concordia.ca/~chvatal/aks.pdf),
printed pages 24-25, selects `k >= 2` using

```text
sqrt(2*(1+ln m)/m) <= (1/5)*k^(-4),   M/32 < m <= M/16.
```

For integer `m >= 1`, dropping `ln m >= 0` and using `k >= 2` gives
`m >= 12800`, hence the necessary condition `M >= 204800`. Requiring the
condition throughout the interval and restoring the logarithm makes the
threshold larger. The geometric, fringe, root, and finite-slope obligations
remain after this necessary screen. This rules out the suggested finite
arities for that proof, not all algorithms built from small M-sorters.
Its asymptotic coefficient as `M` grows cannot be substituted at a convenient
small finite arity. Reprice the feasible finite construction before Lean work.

UB-08's [2024 high-arity paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2024.50)
is useful for its localized-disorder and merge interfaces. The existing local
screen shows that independent binary compilation is not an improvement with
the present base sorters. Keep it as an interface lead; require a new binary
merge/repair argument before promoting it as a numerical route.

## 6. Suggested work order and ticket map

| Order | Ticket | Next finite deliverable |
| --- | --- | --- |
| 1 | UB-07 | Close the user's current tapered schedule and outsider induction; keep 945 conditional until the global theorem. |
| 2 | UB-18 | Extract the actual tapered cuts/ranks and the sufficient provider contract, including frontiers. |
| 3 | UB-14 | A specified final repair plus a deterministic cut lemma and uniform tail certificate; reprice against 140 layers. |
| 4 | UB-15 | Large-width small-fringe screen; retain the distinction from the width-16 provider. |
| parallel research | UB-11, UB-19 | Close ordered-window transfer using signed cut discrepancies and price full forcing/purity. |
| after that gate | UB-20 | A fixed adjacent-region compaction/attenuation macro-stage with a composable transfer and total depth. |
| enabling cleanup | UB-01 | Small generic exact-column-sorter interface. |
| lower priority | UB-05, UB-08, UB-09 | Sweep only after changing a binding contract; retain literature screens and necessary finite constraints. |

UB-17 records this completed source/literature audit. Existing active work
other than the user's identified tapered branch is not reassigned here.
The recommendation is to pursue the final-repair gate for 700 and the changed
transfer/repair channel for 200. There is no new proved coefficient in this
audit, and no claim that either construction gate will close.
