# Final-column repair candidates for the two-round Chvatal pack

Status, 2026-10-10: informal mathematical audit. No construction in this note
is kernel checked, and no improved sorting bound is claimed. The checked
endpoint remains `1770`. This note does not assume that the columns before the
last operation are nearly sorted.

**Correction:** [the lossless-fringe investigation](lossless-fringe.md) shows
that the proposed small-rank premise already confines all marks to fringe
rows before the second scramble. No compactor is needed under that premise.
The arbitrary sparse-compaction discussion below concerns a weaker promise
on final column counts and is not the obligation of that proposal.

## Budget and the semantic target

At height `m <= 2^42`, the first two complete bitonic column sorts cost
`2 * 903 = 1806`. A strict sub-1000 coefficient leaves at most **193** layers
for the final operation. At height `m <= 2^43`, the corresponding figures are
`2 * 946 = 1892` and **107** layers. Any charged routing must be included in
these numbers. The ordinary small-node fallback also has to be reduced from
its present `2016` layers.

The scheduler does not consume sorted columns. It consumes the four fields of
`NodeSpec`: high and low bulk counts at 65 boundaries and high and low fringe
counts for every supported rank. Therefore a repair may be weaker than a full
sort, but it must work for all those thresholds, in both orientations, for the
same fixed scrambles and comparator network.

For a Boolean threshold after the intermediate column sort, write its column heights as
`z=(z_c)`. After the second row scramble `rho`, the input to repair is

    x(r,c) = 1  iff  r is in the bottom z_(rho_r^-1(c)) rows.

This formula, exact total mass, and whatever first-round estimates have really
been proved are the safe preconditions. Calling `x` near sorted is an extra
claim.

## The smallest useful semantic repair interface

Fix a column network `R` of depth `s`, used in parallel on every column. For a
Boolean column `u`, define

    escape_q(R,u) = number of ones among output rows r < m-q.

The immediate interface needed by the existing matrix bridge is:

> **Threshold-count repair.** For every admissible first-round height vector
> `z`, every threshold under consideration, and the fixed second scramble
> `rho`, let `x` be as above. The parallel execution of `R` satisfies:
>
> 1. for every bulk cutoff `i` used by the 65 block boundaries,
>    `sum_c escape_i(R,x_col(c)) <= EB` (with the exact strict/non-strict
>    convention required by the bridge);
> 2. for every `0 < j <= Jmax`,
>    `sum_c escape_f(R,x_col(c)) < eps*j`;
> 3. the analogous two statements hold after Boolean complementation and row
>    reversal, giving the low orientation;
> 4. all four statements use one `R`, one pair of scrambles, and the actual
>    `paperOrdinaryEpsB`, rather than the exploratory `1/59000000` allowance.

Here “admissible” must be spelled out as predicates already delivered by the
first-round common-witness theorem: exact mass, the bulk `L1` bound, and any
separately proved small-rank fringe premise. It must not mean every profile one
hopes is reachable. Once this interface is proved, replacing the last column
sort in `packNodeSpec` is a count argument; no monotonicity of the repaired
columns is needed.

This is the smallest feasible next lemma: first prove the deterministic
**count-to-NodeSpec bridge**, parameterized by `R` and an explicit admissible
state predicate. It isolates the probability theorem and comparator
construction without committing to a false near-sortedness premise.

## Why the current bulk state does not justify band repair

The two-round bulk calculation retains exact mean `i` and

    (1/n) * sum_c |z_c-i| <= e*m.

This gives no maximum displacement in a scrambled column. At `i=m/2`, take
one height `m`, one height `0`, and every other height `m/2`. The mean is exact
and the left side is `m/n`, so the profile satisfies the displayed bound once
`n >= 1/e`. For any chosen row of the second scramble and target column, label
the source selected there as the full column (and choose a distinct empty
column). The target then contains a one at that row, however far above the
middle the row lies.

Thus the class used in the conservative union bound contains states with an
arbitrarily distant stray threshold key. A repair theorem based only on `L1`
cannot assume a narrow dirty band, bounded displacement, or a bounded number
of monotone runs per column.

This example is an obstruction for the **all profiles satisfying the retained
state inequalities** formulation. It does not prove that every such profile is
reachable after the fixed first scramble. A reachability restriction could
remove it, but that restriction would need its own common-witness theorem and
must be carried through the second-round probability count. The current bulk
argument deliberately unions over the larger height-vector class.

The small-rank propagation premise is different and stronger: if
`E_g(z)<eta*j` and `g+eta*j<=f`, then every `z_c<=f`, so row preservation and a
full final sort give zero escapes. In fact, the intermediate columns are
sorted, so their ones already occupy the bottom `f` rows. Row scrambling
preserves those rows; no final repair is needed for these small-rank states.

## Partial sorting and truncated bitonic networks

The repository has a complete bitonic sorter and a depth-`k` bitonic merge on
`2^k` wires. It has no proved shallow arbitrary-input selection or compaction
network matching the interface above.

Some savings attributed to “truncated bitonic” require structure that the
second scramble does not supply:

* If two halves are already sorted in opposite directions, the first
  half-cleaner partitions their bitonic union at the median in one layer.
* If an entire column is bitonic, the first six recursive merge layers divide
  it into 64 correctly ordered regions.
* A second row scramble generally leaves neither condition. It selects one
  entry per row from different sorted intermediate columns. Monotonicity of
  row densities is a distributional fact, not a monotone-run certificate for
  each output column.

Even the optimistic premise that a column arrives as 64 sorted runs does not
immediately fit the budget with the standard merge hierarchy. Merging those
runs through six bitonic levels costs

    (k-5)+(k-4)+...+k = 6k-15,

namely `237` at `k=42` and `243` at `k=43`, before proving that the orientations
and intermediate run structure are correct. These exceed `193` and `107`.
This is a cost obstruction to that particular reuse scheme, not a lower bound
on arbitrary partial-selection networks.

For exact median selection, the familiar truncated construction first sorts
two halves and then uses one half-cleaner. Its depth is
`k(k-1)/2+1`: `862` at `k=42` and `904` at `k=43`. It saves only the final
merge tail and is far outside either repair allowance. Arbitrary fringe cuts
do not automatically inherit even this construction.

## Exact rare-rank capture

Because `eps=1/86000000` and the fringe inequality is strict, every
`j<=86000000` requires zero escapes. Under the small-rank propagation premise,
every intermediate sorted column has height at most `f`, so those marks remain
in the bottom `f` rows after the second scramble. No compactor is needed on
that family. If instead only the final scrambled column counts are bounded by
`f`, without earlier row confinement, lossless sparse compaction would be a
sufficient stronger construction.

For the stronger arbitrary-subset promise, a basic dependency condition is

    f * 2^s >= m.

Indeed the union of the ancestor cones of the `f` destination wires must cover
every input wire, or a unique one outside that union cannot be captured. With
the scheduler ratio `f/m=4095/2^37`, this only gives `s>=26` (rounding the
ratio upward). It does not rule out either budget, but it shows that exact
capture has a real logarithmic charge. Simultaneous capture of every subset of
size at most `f` requires a stronger Hall/routing property; the cone count
alone is not a construction and does not show sufficiency.

A tournament captures a unique maximum in `ceil(log_2 m)` layers, but repeating
it for up to `f` marked keys is sequentially prohibitive. Positive-error
halvers also do not give the required zero leakage. A credible candidate here
would be an explicit lossless sparse compactor whose input family is exactly
the family produced by the two fixed scrambles, together with its depth and
both-orientation proof. No such comparator construction is currently present.

## Sorted-run reuse

The first complete column sort creates sorted runs, but the second row
scramble exchanges individual entries of those runs. It preserves row totals,
not a fixed run in each destination column. Hence there is no sorted final
column core available to feed directly to a depth-`k` bitonic merge.

One could reserve row bands and try to preserve them as runs. That changes the
scramble family and the variance calculation: the cell-level hypergeometric
mgf relies on independent row permutations, while a run-preserving movement
couples many rows. It also has to retain rare-rank capture after keys cross
between runs. Sortedness alone gives neither property. Any reuse proposal must
state the persistent run locations, prove their capture contract at all
supported ranks, and charge initialization plus every merge.

## Candidate versus obstruction

No currently available partial-bitonic, sparse-capture, or sorted-run
construction rigorously fits `193` layers at `2^42`, much less `107` at
`2^43`. The evidence is not an impossibility theorem for shallow threshold
repair. It rules out three shortcuts:

1. deriving bounded displacement from the present aggregate bulk state;
2. applying a truncated bitonic merge without a proved bitonic/run premise;
3. treating the intermediate sorted columns as persistent runs after the
   second row scramble.

The most economical next result is the parameterized threshold-count repair
bridge above. Immediately after it, test the exact small-rank subproblem:

> Given the explicit reachable-state predicate supplied by the proposed
> first-round small-rank theorem, construct one depth-`s` column network that
> sends every marked key into the bottom `f` rows, with `s<=193` (preferably
> `s<=107`), and prove the complemented/reversed version for the same network.

If the reachable-state predicate is only “at most `f` marks per column,” this
is an arbitrary sparse-compaction problem and should be stated honestly. If a
stronger predicate is intended, prove it before designing the network. Only
after exact small-rank capture closes is it useful to add the 65 bulk cutoffs
and the relative-error ranks above `86000000`.

## Verification scope

This was a source and mathematical audit only. No Lean files were changed, no
builds or tests were run, and the numerical candidates above are elementary
depth arithmetic rather than formal certificates.
