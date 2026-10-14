# Can an existing partitioner supply the UB-26 prefix?

Status: source-based feasibility screen, 2026-10-14. No construction or
sorting bound is claimed.

## Required interface

For some fixed `0 < theta < 1`, a prefix on `n` wires must have depth
`p*log2(n)+O(1)` and, for every Boolean input, place all but at most
`O(n^theta)` values into consecutive rank-pure blocks (or produce an
`s`-sorted output with one physical dirty interval of that width). The
rank-pure cleanup price is `p/(1-theta)`; the seam-cleanup price for an
`s`-sorted prefix is `(p+theta)/(1-theta)`. Thus at `theta=1/4`, the relevant
prefix budget is roughly 150 layers per input bit. A count bound on wrong-side
keys, without a physical location guarantee, is insufficient.

## Reuse candidates screened

**Stop the current Chvatal construction early.** The checked `RealBlocks`
proof supplies exact purity only at fixed `2^42`-wire leaves, after the full
repeated schedule. The fractional outsider invariant constrains ranks inside
logical bags; it does not put the remaining errors in consecutive physical
wires. Even granting an optimistic physical rank window, charging the
prefix's existing 1419 coefficient and recursive cleanup cannot beat 1419.
This is a no-go for the simple early-stop reuse, not an impossibility result
for other schedules or new geometric invariants.

**Reuse the 1992 AKS row-scramble/multiway core.** Existing finite screens give
binary cores of 72 or 110 layers for 16- or 32-way cuts, but the proved
all-cut contracts permit 55% or 45% relative leakage. Those count bounds do
not imply rank-pure bins, adjacency of cross-bin errors, or one physical dirty
interval. The retained spill-tail analysis also finds that its proposed
uniform per-column localization is obstructed for arbitrary row permutations,
and the published aggregate estimate does not yield a sparse oblivious
repair. So the small core depth cannot be treated as a UB-26 prefix cost.

**Reuse the direct-multiway profile work.** Its current purpose is to close a
new global rank-profile recurrence around a multiway stage, not to prove
zero-error/pure contiguous blocks after a cheap prefix. The latest transfer
audit still has an unresolved rank-1 boundary-displacement term, and its
stated gate is first below 500. It is structurally closer to the required
all-input rank information than the row-scramble aggregate bound, but it does
not currently furnish UB-26's positional contract or the approximately 150
depth gate.

**Compile the 2024 high-arity `k`-sorting architecture.** The existing screen
shows that replacing each high-arity comparator independently by a binary
sorter does not give the needed prefix: it multiplies the high-arity depth by
the binary cost and loses the advantage. Its structured intermediate states
remain a possible source of a new contract, but no rank-pure localization
lemma is presently in the repository.

## Assessment and next experiment

No existing result can simply be plugged into the rank-pure prefix slot. The
closest reusable ingredients are (i) Chvatal's all-rank profile machinery,
which retains positional geometry only through actual placement analysis,
and (ii) the AKS multiway core, whose depth is attractive but whose current
contract is too weak to compose. Combining them is a new construction and
proof, not reuse of an existing theorem.

The cheapest discriminating experiment is to test a *specific interface* on
the existing row-scramble network: can its fixed permutation family prove a
simultaneous rank-pure block guarantee after aggregating adjacent columns,
with a deterministic oblivious cleanup of charged depth? The current
aggregate contract alone cannot establish this. A useful result would need
an explicit tail/discrepancy theorem and a network that gathers and repairs
the exceptional columns. If that screen fails or the repair costs above the
rough 150-per-bit gate, stop this reuse route and pursue a genuinely new
jointly designed partitioner/scheduler instead of formalizing the local
depth-72/110 cores further.

Claim level: hand-audited source-based screening. This is not an impossibility
theorem; the obstruction is the gap between existing contracts and the
required positional promise.
