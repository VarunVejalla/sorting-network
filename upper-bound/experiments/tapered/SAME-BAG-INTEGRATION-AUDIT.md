# Same-bag separator integration audit

Status: the original standard-parameter provider has a genuine local-size
mismatch. A tuned width-16 provider now covers that missing live-size range,
and a common size-adaptive interface selects it below `2^38` and the standard
provider above. Actual schedule/rank installation remains open (October 13).

## Exact interface mismatch

`large_truncated_padded_witness_exists` requires `2^38 <= a`. Its nearby
rectangle has at least `2^34` rows and at least 16 columns. The row floor is
not arbitrary: `truncated_fringe_bulk_pair_exists` currently requires
`2^34 <= m+1`, while its two-round concentration inputs are proved under
`2^34 <= m`.

The candidate schedule only establishes reference capacities down to `2^34`.
At its meeting frontier the capacity exponent is exactly 36, so the reference
capacity is `2^36`, a factor four below the padded-provider threshold. Actual
occupancy is approximately `(1-2^-24) C` with at most 69 wires of discrepancy,
so it is smaller still. The meeting node is a separate frontier case. Direct
`SameBagScale.lean` now proves a stronger exact statement: for every
`k` satisfying `4*k+8 <= d`, the stage
`t = candidateTf d - (6*k+1)` has an address-zero active bag at the lower
frontier whose reference-capacity exponent is exactly 34. These are distinct
stages, so there are `floor((d-8)/4)+1` such active stages. This is a
kernel-checked linear-size family, not just the numerical schedule scan. The
same module proves `candidateAlpha+2 <= candidateOmega` for every member, so
these bags are in the ordinary interior transition band, not just at the
frontier. It also proves that if the proposed occupancy identity and
`|eta| <= 69` hold there, the actual wire count is strictly below `2^38`;
the current large-witness existence hypothesis genuinely fails for these
scheduled bags.

Consequently the standard `low_fringe_fits_of_scheduled_flow` theorem alone
could not cover those bags. The new `CyclicSmall16PaddedWitness` instead uses
`f=16000`, `J=9000000`, and 16 columns; it is constructed for every
`2^34 <= a < 2^38`, and its 256,016-wire protected prefix fits the minimum
scheduled up-flow. This closes the local witness-scale obstruction for the
fixed-width branch. It does not yet provide one common adapter or prove the
rank invariant for the resulting routed outputs.

## What the numerical certificate says

The first-round union estimate uses `E = 38/10^6` and needs approximately
`log(2(m+1)) + 1/2 <= m E^2`. Direct numerical bisection puts its threshold at
`m = 17,145,533,750` (about `2^33.997`), explaining the chosen `2^34` row
floor. Covering `2^34`-wire bags while retaining 16 columns would need rows
around `2^30`; at that row count the same inequality needs `E` around
`1.4e-4`, nearly four times larger. That changes the second-round
admissibility and final B2 error budget. Merely lowering the
`nearby_rectangle` threshold would invalidate the current existence proof.

More strongly, simply retuning `E` and `lambda` in the *same two-round rate
inequalities* cannot cover a `2^30`-row rectangle. Write
`L = log(2(m+1))+1/2`. Round one forces `E >= sqrt(L/m)`. In round two,
`K = lambda*delta/2 - lambda^2*(1/2+2*lambda/9)*E/2`; since the parenthetic
factor is at least `1/2`, optimizing this quadratic over lambda gives
`K <= delta^2/(4E)`. Hence `m*K <= m^(3/2)*delta^2/(4*sqrt(L))`. At
`m=2^30`, `delta=2^-21`, this upper bound is about `0.43`, while round two
needs at least `L ~= 21.99`. This is an analytic obstruction within the
current rate model, not a failed Lean proof. A lower-size provider needs a
stronger concentration/rate argument or a different construction.

## Fastest useful next steps

1. Keep the checked low/high fringe and separator composition lemmas as
   reusable interfaces, but do not claim same-bag schedule coverage yet.
2. Audit the late-stage schedule to locate exactly how many stages/nodes have
   local sizes below `2^38`, and whether a bounded-depth terminal/frontier
   treatment can absorb them without a linear-in-`d` penalty.
3. For a same-architecture attempt, strengthen the two-round concentration
   inequality itself; retuning only `E` and `lambda` is ruled out by the
   calculation above.
4. In parallel, investigate a construction change: make one certified
   rectangle serve several smaller routed bags, or use a different ordinary
   kernel. Such a merge requires a new ownership and cost analysis; it is not
   supplied by the present `RaggedWirePartition` ownership theorem.

The schedule classification, conditional occupancy comparison, fixed-width
construction, and common adaptive interface are now kernel-checked. Next
instantiate its high/low suffix conditions and cohort ranges from the actual
routed slot profile, and prove the later-stage input-rank bounds. A
frontier-only patch still cannot establish the all-stage invariant.
