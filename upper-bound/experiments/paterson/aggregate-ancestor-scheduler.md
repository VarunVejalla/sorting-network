# Aggregate ancestor-crossing scheduler: contraction and local support

Status, 2026-10-10: informal contraction theorem and necessary interface
conditions, with exact scalar calculations. No new global scheduler or Lean
sorting theorem is supplied.

## Pair contraction above the imbalance floor

At a threshold, let a pair's original errors be `H` high keys on the left
and `L` low keys on the right. Their count imbalance is `Delta=L-H`.
The combined core repair gives

    H' = max(a,b-Delta),    L' = max(b,a+Delta),

where `a,b` are errors left outside the respective cores.
The minimum possible pair crossing error is `|Delta|`, by conservation.
Define the removable excess

    X = H+L-|Delta| = 2 min(H,L).

If the concentrators give the **relative** bounds

    a <= epsilon H,    b <= epsilon L,    0 <= epsilon <= 1,

then

    X' <= epsilon X.

For `Delta>=0`, `b-Delta <= epsilon L-Delta <= epsilon H`, so
`H' <= epsilon H`. Since `L'-H'=Delta`, `X'=2H'<=epsilon X`.
The other sign is symmetric. Integer floors can only strengthen the result.

This refines the previous paired-core audit: imbalance prevents eliminating
all errors, but does **not** prevent relative contraction above its floor.
Fixed-budget bounds `a,b<=epsilon K` alone do not supply this contraction
when actual `H,L` are much smaller or unequal. The existing all-supported-rank
separator interface is designed to provide relative cohort guarantees, but
the proposed recursive concentrator must preserve them at all thresholds.

Exact concentration has `epsilon=0`, attaining the pair's minimum crossing
error. The singleton tournament construction is a concrete instance.

## Candidate aggregate state

For each ancestor cut, retain the threshold-crossing counts

    H_c = # high keys on its positional left,
    L_c = # low keys on its positional right,
    Delta_c = L_c-H_c,
    X_c = H_c+L_c-|Delta_c|.

The cut's global `Delta_c` is fixed by native rank counts and positional
capacity. For the root half it is zero; finer cuts in the upper region can
have the deep-subtree discrepancy already tracked by the legacy proof.
Ordered core compare-splits cannot increase either side's crossing count
at cuts between their blocks, so they cannot increase `X_c`.

A repair of the **entire** two sides of a cut, with a relative all-threshold
core guarantee, contracts that cut's `X_c` as above. A repair of only two
adjacent bags does not: errors outside that pair remain untouched, and its
pair-local imbalance can differ from `Delta_c`. No uniform sweep contraction
follows from monotonicity alone.

A hierarchical scheduler therefore needs a coverage lemma: during one epoch,
every removable crossing cohort is presented to a suitable paired repair,
with enough local support and without reintroducing ancestor crossings.
This is a concrete missing theorem; merely summing monotone potentials does
not prove it.

## Recovery of local stranger bounds

An aggregate state can bound output bins after they occupy ordered positional
intervals. For a bin with lower cut `lo` and upper cut `hi`, its wrong-native
keys are bounded by

    L_lo + H_hi.

This is the route back to the old root-rebuild interface: prove these two
directional cut bounds fit every rebuilt ancestor budget, then any assigned
subset also fits. It requires directional information and the imbalance
terms, not just a small sum of `X_c` over all cuts.

Before final positional allocation, an aggregate bound over many bags permits
all of its errors to occupy one small bag. The current comparison primitive
has a local support precondition. Thus the aggregate state must additionally
guard local extreme-cohort size or provide a separate rebalance/concentration
operation before every primitive call.

## Local support is a substantial limitation

Suppose sixteen equal-capacity leaves each have nominal local stranger
budget `mu*m`. A single sum bound of `16*mu*m` allows one leaf to contain up
to sixteen times the nominal budget. The existing full-bag supported
separator is only certified up to `.02m`, while `mu=.0199`. Its certified
amplification headroom is only `200/199`, about 1.005.

There is also an implementation-independent fringe cardinality condition.
Capturing all but fraction `e` of a supported cohort of size `sigma*m` into
a fringe of size `f*m` requires

    (1-e)*sigma <= f

in the large-size limit. The current full-bag fringe is `f=1/32` and
`e≈.0438354`; it cannot support even an ideal unlimited-depth guarantee
beyond `sigma≈.0326827` with that same fringe. Sixteenfold concentrated
nominal errors would have `sigma=.3184`, which is incompatible with it.

If the ideal full-bag scheduled fringe is enlarged to `lambda*m/2`, then
`lambda >= 2(1-e)*sigma`. The existing capacity identity

    nu = 2 lambda A + (1-lambda)/(2A)

requires `lambda < 1/(2A+1)` for `nu<1`. At `A=4.75`, this bounds ideal
support amplification relative to `mu` by less than approximately 2.503.
Fourfold or sixteenfold concentration is impossible within this ideal
capacity/fringe model at the fixed `A,e`, even before rounding or depth.

These ideal necessary constraints do not prove that every aggregate
scheduler fails: it could use bigger temporary blocks, a different primitive,
a changed allocation identity, or a local envelope. They do show why dropping
the per-bag guard while keeping the current separator is invalid.

## Cost cannot be inferred from error contraction

The exact-core budgets already computed include 295 layers for a 32-key
cohort on a block as large as 305 million wires, and 615 for the dense finest
budget. Paying such repairs at multiple ancestor levels is not competitive
with the 561-layer full root sorter.

Approximate relative concentration is the most relevant cost target now.
It must expose `(core size, depth, relative residual factor)` together.
Stopping recursion once a branch budget is small does not automatically
preserve a relative guarantee for the *actual* cohort, since many branches
can contribute residuals and singleton cohorts require zero leakage when
`epsilon<1`.

There is no justified epoch depth or improved global coefficient from the
aggregate potential yet. Even a contraction certificate needs the coverage
lemma, local support guard, final directional bounds, and actual core costs.

## Recommended next mathematical obligation

Use a **hybrid invariant**: directional ancestor-crossing bounds plus a local
extreme-cohort envelope. Prove one hierarchical epoch's coverage/contraction
while retaining that envelope. Start with a four-block model, where the
distinction between pair-local and ancestor imbalance already appears; do
not assume that sixteen independent balanced pairs exist.

The useful new result is the exact relative contraction of removable excess.
The unresolved structural question is whether a cheap epoch can obtain that
contraction while preventing local cohort overload. Resolving it would justify
a scheduler change; the present analysis does not yet establish one.
