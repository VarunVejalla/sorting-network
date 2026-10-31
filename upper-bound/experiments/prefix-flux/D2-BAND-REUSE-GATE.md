# D2 and UB-34 deterministic band-repair gate (2026-10-27)

## Reusable result

The best reusable UB-34 artifact for the sub-300 route is the deterministic
band-repair contract in `upper-bound/best/AKS/Sub800/MergeBandPack.lean`:

- `mergeBandPack2Net_low_crossings_le` bounds far low-key crossings after the
  band stage by the round-1 profile beyond a source cut.
- `mergeBandPack2Net_escapes_le` gives the corresponding three-term escape
  accounting for a cut inside a band.
- `mergeBandPack2Net_depth_le` prices the added repair as the bitonic depth of
  the segment width.

The D2 worktree has a separate kernel-checked fixed-core area theorem and its
corollary `fullHeightTwoShuffle_column_deviation_le_52` in
`D2Slope25MarginTail.lean`. The latter says every output column height is at
most 52 rows from the exact mean; `fullHeightTwoShuffle_margin_tails_le`
provides the stronger aggregate tail `676/r` beyond margin `r`.

More directly, `D2LiftedShuffleBridge.lean` proves a threshold-count rank
interval of 3392 wires for the actual stride-35/stride-25 semantic core, and
the new `D2PointwiseRankError.lean` converts it to pointwise rank displacement
at most 3392 for any permutation input already sorted within columns. This
closes the fixed-core local displacement gate. It does not show that each
scheduled ragged sender is such a tile or that the displacement composes
through the address routing.

These are promising ingredients, not yet a composed local sorting theorem.
UB-34's network model/module is absent from the sub300 source tree, and the
D2 profile has to be placed at the exact input point of the band operation.
The adapter must also prove column monotonicity there, physical cut conversion,
both crossing directions, edge rounding, and a disjoint set of bands at every
active sender.

## Exact width and crossing arithmetic

The existing UB-34 repair theorem only handles disjoint segments of length
`2^b`. It does not directly price a 56-row band. The immediate supported
choice is a 64-row segment (`b=6`, depth at most 21), centered at an aligned
cut, so its radius is 32 rows.

This is an API limitation, not a depth obstruction: the runaware package has
an arbitrary-size bitonic network with depth at most
`ceil(log2(56))*7/2 = 21`, so a D2-specific 56-row segment can retain radius28
at the same depth. Its segmented-output lemma still has to be proved; the
UB-34 power-of-two interval theorem cannot be applied unchanged.

With the existing 64-row segments, the segment containing output distance80
is the next band above the cut, starting 32 rows above it. L3a charges to the
source tail there; after one row of rounding, `676/31 < 22`, or at most21
integer keys per cut, under its monotone-profile hypothesis.

With the D2-specific 56-row segments centered on cuts spaced64 rows apart,
bands are disjoint and the next band starts36 rows above the cut. L3a then
gives `676/35 < 20`, or at most19 integer keys per cut after rounding. This
is a stronger one-sided coarse allowance at the same 21-layer depth, but
requires adapting L3a to arbitrary segment width56 and proving the actual
cut lattice. Neither coarse calculation gives zero crossings at distance80;
that would need the sharper within-segment escape lemma and a separate bound
on row-scrambled segment contents. In particular, a crossing at distance80
can lie in a neighboring band, so reasoning only about the band centered on
the cut is insufficient.

The local constant 21 is only a one-sided aggregate-per-cut bound, not a
complete sender budget: the opposite direction and every cut traversed by a
key must also be charged. The global scheduler must then propagate these fresh
errors and prove terminal cleanup. No limsup theorem or coefficient below 300
follows yet.

## Pricing and next proof gate

The existing 212.5 and 230 coefficient screens still need their exact macro
network and rank-transfer assumptions audited. The now-checked fixed-core
displacement theorem makes the next global gate more specific: prove that one
actual D2 scheduler transition turns a global displacement bound `W` into at
most `W + 3392` (or a sharper band-repair value), uniformly for every sender,
using its physical address map and child-cut spacing. Iterating this over
`O(log n)` stages would give `W=O(log n)`; the documented block-and-seam
cleanup would then cost `o(log n)`. This one-transition address theorem, its
all-depth induction, and the arbitrary-`n` final bound are still missing.

## D2 physical two-grid gate (2026-10-30)

The sub-300 worktree contains a stronger self-contained Boolean provider than
the earlier UB-34 band adapter: `D2ReflectedPhysicalPack.lean` proves that
the actual reflected `physicalPackTwoGridNet` output, on every Boolean input,
has a common dirty interval of at most 832 wires, and restores column
monotonicity. `D2PhysicalPackTwoGrid.lean` prices this macro at 276 layers
(three 78-layer column sorts plus 42 layers of two-grid repair). At the
candidate schedule rate `5/6`, the conditional stage coefficient is 230,
leaving 70 for all additional routing and cleanup costs. This is a promising
local provider for a Boolean-profile proof; it is not a sorter or a global
recurrence yet.

An attempted value-level upgrade to pointwise rank displacement used generic
`ComparatorNetwork.exec_comp_monotone` on the flattened physical network. The
focused Lean run grew to about 8.6 GB and exceeded the practical resource
budget before completing. That route should not be repeated on the flattened
network. The proof architecture should stay in Boolean threshold profiles:
apply the checked provider directly at each threshold, then prove the
all-depth schedule transition and terminal criterion at the profile level.
The missing critical step remains an exact adapter from each scheduled
sender's physical wires and destination cells to the profile grouping used by
`D2PhysicalProfileGlobalTransfer.lean` / `D2FlowRankBridge.lean`.

## 832-wire band to D2-port branching gate (2026-10-30)

`D2DirtyBandPortBranching.lean` now kernel-checks a local geometric lemma: if
every positive middle child port is at least as wide as a dirty interval, that
interval can intersect at most two of the ten ordered ports (two end ports and
eight child ports). Three touched ports would force the entire middle child
port, plus nonempty pieces on both sides, inside an interval no wider than
that port.

The reproducible finite schedule screen
`python upper-bound/experiments/prefix-flux/d2_dirty_band_branching_gate.py
--depth 100 --scale 8192` checks 1,681,816 positive child ports in 217,470
compressed stage rows. The minimum is 131,072 wires; none is below the
provider's 832-wire band. This strongly supports the local width premise for
the tested `(3,3,2)` schedule but is not an all-depth proof.

This still does not give a global sparse-support recurrence. The fixed
physical provider acts on 4096-by-64 tiles, and a large sender can contain
multiple such tiles; each tile can contribute its own dirty band. The actual
D2 transition must map those clipped tile bands to receiver cells, and the
all-depth schedule must prove the required child-port width and tile-to-port
correspondence. The existing `448-per-tile` profile transfer is the more
appropriate accounting when several tiles occur in one sender.

## Six-stage schedule symmetry (2026-10-30)

`D2SchedulePeriodSix.lean` now kernel-checks the exact arithmetic under
`(t,i) -> (t+6,i+4)`: once the lower frontier is positive, `alpha` shifts by
four; `omega` shifts by two; the candidate capacity and every role-specific
quota are unchanged. The active-set identity is

```text
active(d,tf,i+4,t+6) <-> active(d,tf,i) and 3*i < t+2
```

for `t >= 2` and `t+6 <= tf`. Thus the bulk schedule repeats after six stages
and four tree levels, while one parity-compatible sender at the upper edge
must be treated separately. This is a candidate architecture for replacing
the stage-by-stage reserve proofs with a bulk induction plus a moving-edge
lemma. It does not yet propagate the flow state across that shift or prove
the sender-input reserve contract; the global profile recurrence and sorting
proof remain open. Focused check passed with
`check_prefix_flux_lean.py .../D2SchedulePeriodSix.lean`.

The same module now proves role preservation under this shift for levels below
`omega(t)`, provided the translated level avoids the exceptional strip
`i+2=omega(t)`. Thus the schedule-only bulk transition preserves roles away
from the moving bottom edge. The flow state itself has not yet been proved
periodic under this coordinate shift.

`D2FlowLocality.lean` kernel-checks two locality adapters. First, equal root
triples and ordered child-root deficits determine the post-stage root triple
when local activity, role, and selected quota agree. Second, equal two-level
profiles determine the post-stage root profile (root triple plus eight child
deficits), given matching schedule callbacks at the root and each child. This
is the radius-two to radius-one induction step, including parent overwrites;
the general radius induction and its application to the six-stage schedule
remain open. Focused check passed with
`check_prefix_flux_lean.py .../D2FlowLocality.lean`.

`D2FlowPeriodShift.lean` now combines that callback extensionality with the
proved `(t,i) -> (t+6,i+4)` schedule arithmetic. If every level in a subtree
lies in the bulk strip (away from both frontiers), one concrete recursive
stage on that same input tree is identical under the two shifted schedules.
This proves operator-level conjugacy, not equality of the actual run
subtrees: parent overwrites can give those inputs different states. Focused
Lean check passed for both locality modules.

The more useful depth/time symmetry is now kernel-checked in
`D2FlowDepthShift.lean`: `(d,t,i) -> (d+4,t+6,i)` preserves the candidate's
active bit (through the old bottom frontier), role, capacity exponent, and
quota. By callback extensionality, the one-stage tree operators are equal on
any identical input subtree wholly above that frontier. The reproducible
`d2_depth_shift_profile_gate.py` compares exact signatures at `(d,t,i)` and
`(d+4,t+6,i)`, restricting the entire observed radius to stay above the old
bottom frontier. It supports both normalized distributions and a stronger
same-address-prefix comparison. With shared signature interning, both modes
pass: depth80 radius4 on91 bulk pairs; depth100 radius4 on234, radius8 on140,
radius12 on70, and radius16 on24 pairs. In pointwise mode, every path prefix
at each tested pair has the same profile. These are finite runs; proving the
all-radius relation and its boundary/base cases remains open.
The same file now proves the exact one-step interface:
`d2FlowCandidateRootProfile_eq_of_depth_shift` transfers equal radius-two
input profiles to equal radius-one output profiles under the shifted schedule.
This connects the observed relation to the concrete recursive update, but does
not yet establish its base case or induction over the actual runs.

The exact reachable-reserve audit `d2_reachable_reserve_audit.py --depth 110
--scale 8192` also passed: it checked 273,700 active ordinary senders across
994,746 interned flow states, with no failures in deficit, quota, allocation,
parity, balance, or endpoint-reserve constraints. The tightest deficit ratio
occurred at stage 236, level 80, role `botDesc`, so this extends the finite
support beyond the hand-proved Stage-20 transition. It is still only a finite
check and does not prove the recurring reserve invariant.

`D2StrongFlowStage.lean` now bridges the sharp affine cut lemma to the actual
recursive `d2FlowStage`: assuming one ordinary sender's affine profile,
balance, allocation, parity and endpoint reserves, every concrete child root
satisfies `8192*G_child + 7 <= 30*c` at the doubled child capacity. This
focused Lean check passes. The same file proves the candidate's middle and
bottom-descending quotas exactly saturate `4096*quota=15*capacity`, the
quota half of that affine profile. These close the local tree-update and
schedule-arithmetic adapters. The new recursive predicate
`d2FlowStageAffineInputs` packages the sharp profile together with allocation,
parity and endpoint reserves, and its Lean adapter derives the existing
`d2FlowStageInvInputs`. The same file proves that this affine contract at
every actual stage suffices for the candidate run to preserve the reserve
invariant for any finite horizon. Thus the induction interface is now stated
using the sharper profile directly. The all-stage provider is still missing:
in particular it must propagate endpoint reserves, allocations and the
top-rise zero-root case through the moving frontiers.

That audit now also checks the sharp local profile used by
`D2StrongDeficitPropagation.lean`: top-rise senders have zero root deficit;
mid and bottom-descending senders satisfy `8192*G + 7 <= 15*capacity` and
`4096*quota <= 15*capacity`. At depth 110, all 273,700 ordinary senders pass,
with the minimum normalized affine slack at the same stage-236 witness; the
minimum integer slack is 469,762,048 at stage 161.
Run with `d2_reachable_reserve_audit.py --depth 110 --scale 8192
--require-affine`. This confirms the local affine invariant on the tested
actual run; proving its all-depth scheduled induction remains open.

The audit also checks the exceptional roles separately: all 15,946 `topDesc`
and `botRise` sender states at depth 110 satisfy `low+high=G`, and all 7,153
`topDesc` roots have `G=0`. These checks had previously been omitted from the
script's aggregate pass criterion. They remain finite evidence; `botRise`
needs a tree-transition argument preserving the recursive child state, while
`topDesc` needs the all-depth zero-root boundary proof.

The exact-state screen `d2_period_six_state_gate.py 40 50 60 70 80 90 100 110`
passes all 1,937 tested stage-level pairs after burn-in `t >= 2*d+16`. It
compares exact per-wire frequency distributions, computed by propagating
multiplicities through the shared FlowDAG and normalizing by `8^i`, for
recursive signatures at `(t,i)` and `(t+6,i+4)`. At radius one the signature
is `(root deficit, low, high, all eight child-root deficits)`. Exactly 312
pairs differ, all when `i+2=omega(t)`; every other distribution matches.
Earlier burn-in checks still fail at exactly two pairs for offset 12/depth100
and one pair for offset14/depth110; offset16 passes.

The script now accepts `--radius r`, extending each signature down `r` levels.
The normalized distribution check also passes at radius2 for depths40,50,60;
radius3 for depths40,50,60; radius4 for depths40,50,60,100,110; and radii5
through8 for depth40; radius6 for depths100,110; and radius8 for depths100,110.
At radius r, the only observed mismatches occur when an even-depth descendant
in the signature reaches the moving bottom edge; the script marks those by
`i+2+2*j=omega(t)` for `0<=2*j<r`. The radius8 runs compare 459 and 592
stage-level pairs at depths100 and110, with 242 and 282 edge-strip cases;
every off-edge normalized distribution matches exactly. (At depth40 the
radius5-8 windows all touch the edge, so they give no off-edge evidence.) The
exact signature encoder interns recursive profiles as integer IDs to keep
these checks practical. The checks remain empirical, not an all-depth theorem;
proving the distribution recurrence and using it to close the reserve and
profile transitions remain open.

Extension check (2026-10-31): at radius8 the old `2*d+16` burn-in fails the
script's edge-strip criterion at depths120 and130 (3 and5 mismatches,
respectively; first mismatches at `(t,i)=(256,76)` and `(276,82)`). Raising
the offset to24 passes both depths (621 and774 pairs); offset32 also passes
(510 and650 pairs). Thus the offset16 evidence does not extrapolate to all
depths. This remains a finite screen: it does not identify a uniform burn-in
formula or prove that the extra mismatches are boundary-only.
For the first depth130 mismatch `(276,82)`, a targeted exact comparison finds
equality at radii0 through6 and a mismatch at radii7 and8. This localizes the
disagreement to a deeper neighborhood but does not identify its mechanism.
At depth140, offset16 has15 unexpected mismatches, while offset24 passes all
944 tested pairs. The tested depth120/130/140 results are consistent with a
fixed larger transient allowance, but do not prove one.

Structural implication: the Lean locality adapter maps an input radius-two
profile to an output radius-one profile. Iterating it six times can therefore
propagate a radius-seven equality to a radius-one equality, but consumes one
radius unit per stage. A fixed-radius equality is not by itself an invariant
under indefinite time iteration. The period-six screen can become an
all-depth proof only with an all-radius/coinductive profile relation, or with
a genuinely contracting inequality that closes at fixed radius; more
finite-radius Lean wrappers alone do not close this gap.

Depth-shift extension (2026-10-31): the separate `(d,t,i)->(d+4,t+6,i)`
screen at depth150 with burn-in offset24 has zero normalized-distribution
mismatches at radii8 (690 stage-level pairs) and16 (374 pairs). The test
compares bulk profiles only and is finite evidence; it neither proves
same-address equality nor a uniform transient bound. The Lean schedule
conjugacy is exact, but a run-level argument must still absorb the six-stage
startup discrepancy and handle the moving bottom boundary.
