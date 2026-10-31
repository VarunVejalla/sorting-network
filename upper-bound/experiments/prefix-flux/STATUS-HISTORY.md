# Archived chronological research log

This file preserves the former long-form `STATUS.md` without edits to its
research entries. It includes superseded candidates, finite screens, and
stage-by-stage progress notes. Do not use it as the current proof status;
start with [HANDOFF.md](HANDOFF.md) and [README.md](README.md).

---

# UB-42 status (historical opening entry)

2026-10-27: `D2StaticWireSets.lean` now kernel-checks the D2 eight-child
static-hole fit criterion. If each child's low/high deficits balance its
root deficit, each root deficit is at most the native child width, the
parent's two fringes are at most one child width, and the first/last child
fronts fit those fringes, then every child interval lies in its native slot
and all eight holes fit in the parent interval. Saturated children are
represented by empty point holes at a parent edge. This discharges the
generic geometry step for `blockOf_staticHoleList`. The companion
`d2EightChildHolesFit_of_two_front_cut` now instantiates it with the actual
`d2FlowCutChild` operation: if the left front fits in child 0, the right tail
fits in child 7, the two fronts do not overlap, and child sizes fit the native
width, then the post-cut holes fit the parent interval. Thus the local cut
identities themselves are no longer a gap. Finally,
`d2EightChildHolesFit_of_flow_reserves` derives those front-fit and
nonoverlap premises from the ordinary sender bounds at the correct scale:
parent native capacity is `8 * width`, `512 * G Ã¢â€°Â¤ 8 * width`,
`256 * quota Ã¢â€°Â¤ 8 * width`, and each endpoint child has the required
`8 * width Ã¢â€°Â¤ 128 * childDeficit` reserve. It also uses the child native caps
to bound the total deficit by `8 * width`. Thus the local geometry now follows
from the same numerical gates as the D2 flow invariant. The new
`d2FlowStageInvInputs_static_holes` theorem extracts the balance, quota,
deficit, and endpoint-reserve gates from the actual ordinary-sender
`d2FlowStageInvInputs`, and extracts child native caps from `d2FlowTreeInv`;
assuming the schedule's native-capacity identity, it proves the static-hole
fit for every active ordinary sender. The remaining local bridge is to
identify the translated rank slices with the actual next-stage bags. Focused
Lean check:
`lake env lean ..\prefix-flux\D2StaticWireSets.lean` from `runaware` with
`prefix-flux` added to `LEAN_PATH` (passed after the final edit).

The theorem `d2FlowStageInvInputs_static_holes` was added after the earlier
status note: it takes the actual recursive `d2FlowTreeInv` and active
ordinary-sender `d2FlowStageInvInputs`, plus the schedule identity
`cap i = scale * 8^(h+1)`, and proves these local hole-fit premises directly.
Its proof uses `d2FlowTreeInv` for every child's native deficit cap and
unpacks the actual stage-input contract for all three ordinary roles. Thus
the local static-gap decomposition is now available at an arbitrary
invariant-satisfying ordinary sender. What remains is the global ownership
induction: prove these parent-complement sets are exactly the source bags,
that the ordinary rank-sliced pieces coincide with each next-stage bag, and
handle inactive, top-descending, and bottom-rising nodes in the same map.

Research-priority correction (2026-10-27): this local address result does not
change the decisive status of the candidate. The arbitrary-root coupled LP in
`D2-DISTANCE-TAIL-PERIOD-GATE.md` still admits terminal error; its tested fixed
linear potentials also fail on longer phase windows. Further routing Lean is
not currently the highest-value step. First close a reviewed arbitrary-root
ordered rank-profile transfer that includes the actual first-sort dominance
and a priced root provider, or reject the nominal `292.5` route. Any future
physical-bag theorem must be attached to that transfer rather than counted as
evidence for the global recurrence.

2026-10-27: `D2StaticAddressPartition.lean` kernel-checks that monotone
cumulative boundaries partition any finite set into disjoint rank slices of
the stated widths. Its first D2 instantiation partitions the *child deficit
mass*, not a physical sender bag (which has size `total-G`). The more relevant
`d2FlowStage_regular_rank_port_conservation` theorem now proves that, for an
ordinary active sender, its two half-up ports plus the eight post-cut down
blocks sum exactly to its actual allocation `total-G`. This is the correct
width invariant for slicing the sender's sorted wires. The focused Lean checks
of `D2StaticAddressPartition.lean` and `D2FlowRankBridge.lean` passed.

The same local partition interface now covers all three special active flow
roles: `top_desc_sender_piece_partition` routes the full sender to its
children when its root deficit is zero, while
`bot_rise_sender_piece_partition` routes the full sender to its parent when
the children are inactive in that stage. The latter uses the exact
`d2FlowStage_botRise_child_root_deficit` identity. Both proofs compile with
the ordinary-sender theorem. This is still a per-sender statement; global
source-bag address realization and the rank recurrence remain open.

The new `routedTargetPiece` groups a sender's local pieces by an arbitrary
next-stage destination map, and
`routed_local_destinations_preserve_partition` proves that these grouped bags
again partition all wires whenever the source bags partition and each local
destination family partitions its sender. This is the compositional stage
lemma needed to use the ordinary/top-descending/bottom-rising local results.
The remaining routing obligation is now explicit: define the schedule's
actual source-bag family and target map (including inactive senders), then
prove each local destination tag maps to the correct next-stage address.

`D2WirePartition.lean` also kernel-checks the one-stage conservation rule: if
current sender bags partition all wires and each sender's pieces partition its
bag, assigning pieces to next-stage bags preserves coverage and pairwise
disjointness. The remaining bridge is to instantiate those pieces from the
D2 flow boundaries and prove the concrete target map, including interactions
with inactive bags. Physical routing, the global rank invariant, and sorting
remain open.

`D2OrdinaryRankRouting.lean` now packages the local map in exactly that form:
both end intervals are one parent piece, each middle rank interval is one
child piece, and the family covers the sender set with pairwise-disjoint
pieces. The parent piece takes its right endpoint explicitly as `rightStart`,
so it matches the flow theorem's `s.card - quota/2` endpoint without an extra
normalization step. The theorem `regular_stage_sender_piece_partition`
instantiates the generic partition directly with the post-transition D2 child
widths and proves that one ordinary sender's rank slices form this local
parent/child partition. Focused Lean compilation passes. The all-node
destination map and compatibility with inactive/special-role bags are still
unproved.

The sender-set instantiation is now explicit in
`d2FlowStage_regular_sender_rank_ports_cover`: for any finite set whose size
matches the allocation, the two half-up rank intervals and the eight
cumulative post-cut down intervals cover that set exactly. It uses the actual
ordinary-stage flow conservation lemma, so the middle widths are the child
allocations `old child deficit - new child deficit`. This still does not prove
the all-node target map or identify the resulting sets with the scheduled
next-stage bags.

Correction, 2026-10-27: the companion theorem
`d2FlowStage_regular_sender_rank_ports_disjoint` now proves the missing local
disjointness: the union of the two up-end slices is disjoint from every child
down slice, and distinct child down slices are disjoint. Together with the
cover theorem, this proves an actual ordinary sender's sorted wire set is
partitioned into its parent and child destinations. The one-stage family
conservation theorem can now be applied once the all-node target map is
defined. Inactive, top-descending, and bottom-rising nodes and the global
stage-to-stage bag correspondence remain open.

`D2StaticWireSets.lean` now kernel-checks the initial top-descending address
case: the eight child rank slices from the full wire universe equal their
respective contiguous static address intervals. This concretely connects the
local rank-routing interface to physical addresses for that first stage only;
it does not establish address correspondence at later stages or resolve the
all-node destination map.

The same file now proves that a rank slice of any contiguous static sender
interval `[lo, hi)` is exactly the translated address interval
`[lo + start, lo + stop)`, provided the stop rank stays within the sender.
The interval cardinality is also exact when `hi Ã¢â€°Â¤ n`. The file now gives the
static address form of `destinationPiece`: child-tagged pieces translate their
two rank boundaries, and the two parent end pieces translate to the matching
left and right intervals. These adapters apply when a sender bag is one
interval. General D2 bags may be unions of intervals; the schedule must still
prove sender-bag geometry and match routed pieces to the next-stage bags.

`D2StaticWireSets.lean` now kernel-checks `blockOf_union_ordered`: a global
rank slice of two ordered finite components splits at the first component's
cardinality and translates to local slices in each component. Its interval
specialization handles a sender bag with one interior gap. The new recursive
`blockOf_orderedRuns` theorem gives the exact prefix-size offsets for a finite
list of ordered components. `staticGapRuns_union_eq_complement` and
`staticGapRuns_ordered` prove that removing any finite ordered list of child
intervals from one parent interval yields exactly such ordered gap runs;
`staticGapRuns_length` gives one more run than holes. Thus eight child holes
give the nine-run representation used by the D2 bag model. The remaining
`blockOf_staticGapRuns` composes these facts and gives the exact rank-slice
address list for the parent-minus-child bag. `staticHoleList_fits` derives the
recursive fit condition from endpoint bounds and pairwise ordering, while
`blockOf_staticHoleList` exposes the combined port-slicing result directly for
an endpoint family (including eight child intervals). The companion
`staticHoleList_fits_of_slots` derives pairwise order from ordered native
slots, leaving only containment of each child run in the parent run as a
schedule premise. The focused Lean check of `D2StaticWireSets.lean` passes.
The actual candidate must still prove that containment and identify the
resulting ports with next-stage bags.

`D2Slope25MarginTail.lean` kernel-checks that the D2 fixed-core variance bound
yields a deterministic margin-tail estimate that may feed UB-34's localized
band-repair lemma. More strongly, it proves every fixed-core output column is
within 52 rows of the mean, so the excess tail is exactly zero beyond 52;
with radius-28 bands, L3a would forbid row-aligned crossings at distance 80
or more. Replacing the candidate's last 78-layer column sort by a 21-layer
band stage, while retaining its 21-layer sparse-edge repair, prices at 230
before terminal cleanup. This is a cost screen only. Its schedule gates are recorded in
[`D2-MARGIN-TAIL-TRANSFER.md`](D2-MARGIN-TAIL-TRANSFER.md).
The exact sparse-bottom FlowDAG screen also passes the abstract disjoint-band
spacing test at depths 25, 50, and 100 for both scales 4096 and 8192; every
positive block lies on the scale lattice, and the smallest gap is 64 rows,
above the 56-row requirement for radius 28. Physical address realization and
an all-depth lattice/spacing proof remain open; reproduce with
`d2_band_spacing_gate.py`.

## Correction to the 2026-10-24 global-prefix LP note

The recent zero-terminal-error LP runs at depths5/6 fixed the root to the
already sorted profile (`root_error=0`, `root_tail=False`); their exact dual
certificates only verify that trivial fixed point. They are not evidence for
sorting arbitrary inputs. With arbitrary-root `--root-tail`, all eight
certified distance-tail caps still allow 6,390 terminal wrong keys in the
depth2 integer selected-cut model (largest block2,082). The analogous depth5
candidate gate with stride64 returns HiGHS `Unknown / primal Basic`. See
[`D2-DISTANCE-TAIL-PERIOD-GATE.md`](D2-DISTANCE-TAIL-PERIOD-GATE.md).

## New checked progress (2026-10-23)

The larger actual-grid adversarial run completed on 2026-10-24. For the
`(3,3,2)` / row-height-8192 candidate, depth5 (four transitions),
`--ordered-prefix --root-tail --seam-defect-fraction 17/2000` gives an
optimal continuous LP with 49,281 variables and 138,710 inequalities. The
maximum terminal wrong mass is 1,731,338 (largest single terminal block
537,991); the threshold prefix defect falls from 3,763,184 to 1,797,850,
but the final profile has 63 terminal blocks with positive relaxed error.
The LP is fractional and its rounded profile is infeasible. This is therefore
not a comparator-network counterexample. It does establish that the selected
13-bit rank-tail root envelope plus the `17/2000` per-sender seam budget is
too weak, even with ordered global profiles, to force the terminal exact-count
contract over these four transitions. The alignment trace also grows during
the run (reaching about 1.74 million at stage3), so tracking only central
threshold defect or summing this seam allowance will not close the gate.
Next test the stronger whole-tail transfer on the same actual row height; if
that still admits positive terminal error, the recurrence needs a spatially
weighted alignment state rather than another scalar tolerance adjustment.

The first propagated-tail follow-up (2026-10-24) used the same flow scale,
row height512, depth4/two transitions, all active full-row cuts, the
`17/2000` seam cap, and a per-sender whole-tail gap of64. HiGHS reached its
120-second limit with a feasible MILP incumbent (relative gap about3.59%);
the selected continuous profile has terminal wrong mass about1.419 million,
including one terminal block with524,288 wrong keys. Its threshold defect
falls from1,602,488 to950,579, while alignment grows from zero to775,817.
The row profile is fractional, so this is not a concrete input or a network
counterexample; the solver did not prove optimality. It is a feasible witness
to insufficiency of this particular finite whole-tail/seam LP interface.
The actual row-height8192 depth5 whole-tail test remains in progress. A direct
adversarial-solution residual check should be added before relying on further
time-limited MILP incumbents.

Integer check of the same interface, depth3/two transitions, row height16,
with all active row cuts and whole-tail gap2, then solved to optimality. Forcing
every profile and count variable integral still gives 220,367 terminal wrong
keys (maximum 43,690 in one block); the rounded solution passes every model
constraint. The computed equality residual is zero and maximum inequality
residual is about1.1e-7, within the solver tolerance. This rules out profile
fractionality as the sole explanation for the coarse interface's failure.
It remains a state-transition witness for relaxed local contracts, not a
single common-witness comparator construction or a counterexample to sorting.

The run-aware D2 scratch formalization now proves the actual transitions through
stage nine: `d2FlowCandidateStage9_preserves_inv` carries the saturated-aware
tree invariant through run stage 10 for every `d>=11`. This includes the
stage-eight root, level-two, and level-four gates, then the stage-nine root,
level-three, and level-five gates. Native level-six reserves in the stage-nine
input are also checked, and Stage 9's bottom-rise makes the actual Stage 10
level-five roots native. For stage ten, the frontier, local level-four
`botDesc` gate arithmetic, and actual level-four gates are checked. The
level-two mid gate's quota parity, capacity ratio, and endpoint-mass arithmetic
are also checked conditionally, but its actual sender-cap and endpoint-reserve
inputs from the Run 10 tree are not yet derived. The level-two/root gates and
preservation through stage ten remain open. The work
is still a finite-phase bridge, not an all-stage induction or limsup theorem. See
[`D2-STAGE9-BRIDGE.md`](D2-STAGE9-BRIDGE.md).

The coupled-profile LP gate has been corrected for an important modeling
issue: exact-sorted-root runs are tautological fixed-point checks, not evidence
for arbitrary inputs. With the 13-bit root-tail envelope, the relaxed terminal
wrong mass is2.2425% at depth4 and2.2401% at depth5; depth4 is unchanged under
three denser row grids. These are failures of the current relaxed contract,
not counterexamples to the fixed network. Depth6's LP returned a numerical
unknown status. See [`PROFILE-GATE.md`](PROFILE-GATE.md). The LP also omits the
baseline-conditioned whole-tail inequality from the actual input profile,
so the positive optimum does not yet isolate a failure of the local error
budget. A follow-up adds these root-conditioned tail inequalities at every
sampled baseline and carries them through the ordered global profile. At depth4
with `(3,3,2)`, 12-bit rows, and row stride256, gaps256 and1024 still yield a
positive terminal objective in the relaxed LP; the largest single rounded
terminal error is202,538 wires. (The reported63 counts objective-eligible
terminal blocks; it is not a count of impure blocks.) The LP profile is
fractional and its rounded profile is infeasible, so this is only a relaxation
diagnostic, not a counterexample to the fixed provider. Root-conditioned tail
control alone is insufficient in this relaxation.

A follow-up tests the hybrid budget: full-row defects sum to at most
`epsilon*bag_size`, while pointwise `epsilon_seam*minority_mass` bounds are
imposed only at D2 port boundaries. The exact full-row sum uses a piecewise
linear formula in sender mass, encoded with binary segment selectors; all
count/profile variables remain continuous. At depth4, `(3,3,2)`, and 8-bit
row height, `epsilon=1/100` and `epsilon_seam=17/2000` give LP objective
34,131.4 and largest rounded single-terminal error29,698. The sorted witness
satisfies the constraints, but the optimizer is fractional and its rounded
profile is infeasible. Thus even this stronger relaxation does not certify
terminal purity, but it is not a counterexample to the fixed network. The
small row height is only a diagnostic; it is not the 13-bit candidate.
Reproduce with `coupled_rank_lp.py --depth 4 --scale 8192 --threshold 1/3
--ordered-prefix --root-tail --all-row-dominance --row-stride 1
--aggregate-defect-fraction 1/100 --seam-defect-fraction 17/2000
--params 3 3 2 --row-bits 8`.

I also imposed the mass-sensitive random-core expectation formula itself as an
optimistic per-sender cap, maximized over each feasible mass segment, with the
same seam caps. This uses650 binary segment selectors; the sorted witness
passes exactly. The relaxed terminal objective is still35,671.2 (largest
rounded single-terminal error30,909), with fractional optimum and infeasible
rounding. Since an expectation bound is not an all-input cap, this cannot
refute the local core; it does show that this scalar mass-sensitive envelope,
even when granted as a hard contract, does not close the present global
relaxation. The next mathematical gain must retain cross-stage alignment or
stronger profile correlations, rather than only tighten the aggregate mean.
Reproduce by replacing `--aggregate-defect-fraction 1/100` with
`--mass-sensitive-mean` in the command above.

The LP now reports the exact threshold-cut decomposition
`F_t(q)=alignment_t+within_bag_defect_t` for its selected profile. In the
mass-sensitive-mean run above, the three stages have `(F, alignment, local)`
approximately `(644520,0,644520)`, `(48452,30909,17543)`, and
`(30909,30909,0)`. The identity residual is below1e-9. Thus the final
obstruction in this optimized profile is entirely cross-bag alignment after
the local bags have become sorted at the threshold cut. This is a finite
fractional-relaxation profile, but it pinpoints the missing contraction
quantity. The next gate is the all-depth transfer of `alignment_t` through
the actual D2 phases, using the port imbalance identities in `PROFILE-GATE.md`.

The LP now has `--propagated-tail-gap f`, which applies the mass-conditioned
whole-tail envelope through every active sender using its actual input profile
from the ordered global `Z_t`; both zero-tail and reflected hole-tail bounds
are imposed. The sorted fixed-point witness passes. At depth5 with row height
16 and `f=8`, the LP gives `F_t(q)=5,164,989` at all five snapshots. The
cross-bag part oscillates from0 to760,567 to5,164,989 to5,110,031 and back to
5,164,989, while the within-bag part supplies the difference. Its
distance-weighted sorted-bag inversion proxy is about`4.83e13, 1.17e14,
1.21e14, 1.18e14` from stages1 through4. The model is fractional, only four
stages, and uses a tiny row height, so this is not an obstruction to the
candidate network. It does show why a central `F_t(q)` contraction alone is
too weak: the needed potential must track the spatial distribution of the
misalignment band. For integer profiles this distance sum is exactly the
inversion count after sorting each bag separately; the piecewise-linear
extension used by the LP was checked against `rank_distance_sum` in18,898
small interval/mass cases. The depth5 solve with row height16 and `f=4` timed out
without an incumbent; it supplies no further evidence.
Reproduce the successful screen with `coupled_rank_lp.py --depth 5 --scale
8192 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance
--row-stride 1 --seam-defect-fraction 17/2000 --propagated-tail-gap 8
--params 3 3 2 --row-bits 4 --time-limit 120`.

## Current route assessment (2026-10-22)

No route yet has a complete proof below300. The most promising current
construction is the unsaturated `(3,3,2)` D2 flow with ragged 13-row waterfill
columns: its three-sort stage cost is273, and its stage/log rate is1, so its
conditional limsup coefficient is273. This is distinct from the `(2,3,2)`
12-bit alternative, whose cost is234 at rate5/4, giving292.5. Conditional on the corrected
`279/256` sender factor, its profile feasibility and median-cut geometry close
on paper; exact flow audits now check the botRise predecessor identity through
depth100. However, the `279/256` factor is still conditional: proving that the
two fronts do not cross is insufficient to show each front fits in its end
child. Those endpoint-containment inequalities have only finite evidence
(204,348 distinct DAG states through depth100), and the two-step induction
cannot yet assume unsaturated cuts. A candidate `c/128` endpoint-reserve
invariant now closes this circularity on paper and passed independent
read-only review, conditional on completing the all-depth schedule partition
and proving exact recurrence correspondence. Some schedule cases now have
scratch Lean proofs, but the full partition and recurrence connection remain
unproved. The f=13 F2
interval screen at the candidate `n>=3832` floor passes
with `eps_F=1/3`; a new rational bracket closes the previously loose closed R1
sum in the interval checker. Still open are the all-depth dimension/sender
proof (including Lean formalization of the log bracket), local common-mask
provider formalization, the global rank recurrence, and the root/terminal
sorting contracts. An inversion-cleanup screen with candidate local
parameters passes its `theta<=27/301` finite threshold at depths64,72,80 but
fails at24,32,48,56 and shows large phase variation; it is an input-dependent
oracle, not a uniform recurrence. See `INVERSION-LOCALIZATION-GATE.md`.

The reserve schedule interface is now partly kernel-checked in the experimental
scratch module `D2ScheduleReserve.lean`: parity-subsequence monotonicity excludes
a top-descending predecessor for an ordinary current sender, exact
frontier inequalities characterize active membership, the bottom-rise boundary
forces the exact adjacent `omega` drop, and a `c/128` child reserve implies
both cut fronts fit under `G<=c/512` and `pi<=c/256`. It now also proves that,
for every `d>=7`, the rounded frontiers stay separated for `2<=t<3*d-14` and
meet at `t=3*d-14`; thus the candidate schedule horizon has stage/log rate1.
It also proves the schedule-level parent closure for active non-top-descending
senders and excludes a `botRise` parent. The ordinary end-child updates now
have kernel-checked normalized forms `g/2+rho/4` and `rho/4`, which preserve
`g<=1/512` assuming `rho<=1/256`. The `botRise` boundary now also gives the
exact native-size/capacity ratio `1/256`; together with allocation<=native,
this supplies its exceptional port bound. The native allocation inequality
is now derived from conservation and eight child native-size caps, with the
Nat-to-Rat capacity match checked; this composes to the `botRise` port bound.
The scratch module now defines the five-way role classifier directly from the
rounded schedule frontiers and derives `3*i=t+6` from the `botRise` role, so
the role-port theorem no longer needs a separately supplied boundary fact.
This remains conditional on native allocation and does not yet connect the
classifier to the actual D2 recurrence.
The one-step `g` propagation interface is now role-complete: every active
non-top-descending child has an active parent, and schedule arithmetic limits
that parent to `topDesc` or one of `topRise`, `mid`, `botDesc`. The local
reserve/cut estimate is proved uniformly for all three ordinary roles, while
`topDesc` clears the child. Composing these facts proves the child
`g<=1/512` bound at its next capacity, assuming the parent state caps, endpoint
reserves, and exact local update equation. This is an all-depth schedule and
local induction step, but it does not initialize or globally induct those
state hypotheses.
The same schedule module now proves that a regular active sender at `t>=4`
before termination has an active same-level predecessor at `t-2`, whose role
is ordinary or `botRise`; `topDesc` is excluded by parity-subsequence
monotonicity of the top frontier. The regular-role port range
`15/4096 <= pi/c <= 1/256` is also kernel-checked. This supplies the schedule
partition and quota constants needed by the endpoint-reserve induction; the
state transfer and startup initialization still need composition.
For processed stages `t<tf`, it now also proves that a `botRise` intermediate
child forces both the current sender and the same-level `t-2` predecessor to
be `botDesc`, matching the exceptional branch of the `279/256` split.
For any active parent whose role is not `topDesc`, the rounded schedule also
excludes both top roles at the intermediate child, leaving exactly `mid`,
`botDesc`, or `botRise`; this supplies the schedule partition for the other
side of the factor split.
The scratch model now includes the exact per-child role update from the D2 cut
rule (`topDesc` zeroes, `botRise` preserves, ordinary roles store the two cut
lengths) and proves native-deficit preservation under noncrossing cuts. This
is a local recurrence lemma; the remaining induction must still establish its
preconditions on every reachable tree state.
It is now packaged with the exact eight-child conservation/update equations:
under child-native bounds, `pi<=a`, and disjoint fronts, one local node step
preserves the parent and all eight child native caps.
The natural-number `c/128` reserve lemma is now composed with conservation
and `pi<=a` to prove full ordinary-cut validity: the fronts are disjoint and
each lies inside its designated end child. Thus cut containment is reduced to
the proposed reserve/state bounds rather than left as a separate circular
assumption.
The ordinary two-stage reserve transfer now explicitly consumes the exact
half-port left by a contained endpoint cut, the quota floor `15/4096`, the
capacity ratio16, and nondecrease through the intermediate child update. The
intermediate node update is now defined directly as inactive-preserve or
active-add-up-port and its monotonicity is kernel-checked; schedule parity also
proves the level-i parent of these children is inactive at that intervening
stage.
Both concrete endpoint-cut lemmas are now composed with this transfer, so a
contained first or last child cut yields the `c/128` reserve after the
intermediate child update.
The local cut update is also reduced to its exact per-child outcomes: the
first child stores the left front, the last stores the right-front distance,
and an interior interval missed by both fronts receives zero deficit.
Combining those formulas with `G<=c/512`, `pi<=c/256`, and the endpoint
reserves proves the actual one-step child invariant `G_child<=2c/512` for all
eight children. Thus the paper's normalized `g<=1/512` update is now checked
through the integer cut rule itself, conditional on the inductive sender and
reserve bounds.
The port side is also composed: eight child-native bounds plus the exact
allocation equation imply allocation<=native, and schedule role geometry then
gives `pi/c<=1/256`.
At the next ordinary visit two stages later, the child native size is exactly
`c/128`; schedule lemmas put those child levels outside the active interval at
all earlier stages and through the following stage. At the boundary stage the
parent is the designated `botRise` case, whose flow update must leave the
children untouched; the recurrence connection is still needed to turn this
schedule history into a native-deficit reserve. The candidate schedule also
has no active leaf before termination.
The scratch Lean model now includes both ways a child deficit can change: its
own active up-port and an overwrite by its parent cut. It proves that the
children of a `botRise` parent stay inactive throughout the two-stage window,
that the parent is inactive before and between its `botRise`/next visits, and
that the `botRise` update preserves its children. From native initialization
and the exact conservation equation at both visits, it derives the exceptional
`gOld+rhoOld=1/256` split and the two-step allocation identity; with the
current `g` and port caps, this yields noncrossing. The scratch module compiles.
The remaining formal gap is to connect its per-child trace and conservation
interface to the complete recursive `FlowDAG` state and prove the current caps
for every reachable sender.
A five-role port interface verifies the remaining constants. Generic cut
arithmetic proves disjoint fronts remove at most each child's deficit, the
contained end cut contributes at least half the old port to that endpoint, and
ordinary quota `15/4096` plus the two-stage capacity factor gives the needed
current `c/128` reserve. Conservation plus `pi<=a` preserves the parent's
native-deficit cap. The two-step identity also gives strict noncrossing margins
`(a-pi)/c>=27/512` after an ordinary predecessor and `>=29/512` after a
`botRise` predecessor, assuming the proposed state/port bounds. The ordinary
two-step identity itself is now proved in the standalone eight-child rational
model, with endpoint `theta` and intermediate port terms summed explicitly;
the capacity formula independently verifies its factors 16 and 32.
The corrected `279/256` factor is now separately kernel-checked from that
identity under two role-split hypotheses: either old quota `<=15/4096` with
exceptional child-port term `<=1`, or old quota `<=1/256` with ordinary
child-port term `<=15/16`.
The experimental Lean module now also defines a depth-indexed eight-ary tree,
the full-subtree initialization, a sentinel-aware native-deficit invariant,
and a recursive stage function with the actual rounded D2 activity/role and
integer-quota callbacks at scale8192. Kernel-checked schedule matching proves
active roles and fixed integer quotas agree with the rational formulas; active
capacities have exponent at least20. Bot-rise uses the live allocation
directly. Leaves are proved inactive through the candidate horizon. The root
index is `d` and its initial allocation is exactly `8192*8^d`. The invariant
also requires each non-leaf deficit to be covered by its child deficits; a
node lemma extracts the exact allocation equation from this condition. The
strengthened initial invariant and module compile. Prefix-sum child positions are proved
contiguous. The cut lengths telescope across the eight intervals, giving an
aggregate ordinary-cut theorem: under balanced parent endpoints, even quota,
in-range fronts, and noncrossing fronts, the sum of new child deficits is
exactly `G+pi`. Tree projection lemmas identify the ordinary child cut,
top-desc clear, and bot-rise preserve branches with their local formulas.
The aggregate identity is composed with the actual recursive transition for
all three ordinary roles (top-rise, mid, and bottom-descending). One-stage
invariant preservation remains open. The transition uses total natural
subtraction, so allocation conservation, quota parity, and valid cuts are
still preconditions to correspondence with `FlowDAG.step`.
Showing endpoint containment for every reachable state and proving the full
invariant induction remain open, as do the provider and global rank recurrence.
Exact `FlowDAG` scans at scale8192 found no reachable child-cover violation
through depth100 (373,240 non-leaf states checked at depth100); this remains
finite evidence only.
Lean also proves root-deficit monotonicity for every recursive stage. As a
result, child-cover is preserved by inactive nodes and `botRise`; for ordinary
roles it is preserved as equality under the already stated cut hypotheses,
and `topDesc` preserves it under its `G=0` guard. Native caps, endpoint
reserves, and reachable proofs of those guards remain open. In addition,
`botRise` preserves the parent native cap from child native bounds and
child-cover, since its updated deficit equals the old child-root total. For
ordinary active nodes, a conditional full-tree-invariant preservation theorem
now composes recursive child invariants, aggregate cut conservation, and the
explicit local parent/child native caps. A companion theorem derives the cut
front fit and those caps from the established endpoint-reserve lemma, provided
quota is within the actual allocation and sender/endpoint bounds hold. A
candidate-specific bridge converts the normalized schedule-port inequality
into that exact integer quota/allocation condition and composes it with stage
preservation. Proving the normalized port and reserve premises for reachable
states remains open.

The accepted Lean Chvatal flow package is specialized to
`(k,A,nu)=(64,4096,1/64)`. The new scratch tree model is parameterized over
stage callbacks but still needs the actual `(8,8,1/4)` schedule and reachable
state proofs before these sender lemmas can connect to a sorting-network
theorem.

Follow-up phase diagnostics at depths80,96,112,128,144 all end below the
`27/301` exponent gate in the same band-initialized oracle, with exponents
`.08494,.07108,.05233,.04696,.04884`. Large drops occur at a single moving
`botDesc` bag, with stage plateaus between descents. The finite screen is
stronger than the prior depth80-only evidence, but the residual remains
nonmonotone and no all-depth or fixed-provider bound follows; see the phase
diagnostic in `INVERSION-LOCALIZATION-GATE.md`.

The two `botDesc` visits at `t=3i-4,3i-2` now have exact state-sensitive
allocation and end-block formulas in `D2-PHASE-IDENTITIES.md`. The audit
`d2_phase_identities.py --depth 100` checks all 14,097 distinct compressed
phase-state rows and their child deficits/end cuts at scale8192. This replaces
the trace's special zero-deficit port fractions with a compact `(G,low,high)`
state description, but the local-tail-to-global recurrence and fixed provider
remain open.

`PROFILE-GATE.md` now also gives an exact all-cut transfer inequality for the
next-stage bag-mass alignment: its increase is bounded by the sum of local
prefix defects at the actual port cuts. This is additive rather than
contractive, but it identifies the quantities that the 13-row tail event must
control and makes the remaining area-potential gap explicit.

The same note now decomposes global inversion exactly into the bag-sorted
inversion plus local prefix defects weighted by gaps between consecutive
static wires. Signed port endpoint defects give the exact perturbation of the
next bag-mass term, with each mass shift priced by its distance from the
threshold. This avoids losing signs in the area accounting, but no all-profile
tail bounds for the weighted terms or distant-bag decay are proved yet.

A follow-up profile screen shows the alignment part need not stay zero: for
left/right root bands it spikes at stage1, with sampled `log_N(alignment)`
growing from about1.34 (`d=32`) to1.65 (`d=64`), before the terminal inversion
exponent falls below.09 at `d=64`. Therefore it cannot be charged as a small
startup additive term; the global recurrence must contract alignment and
local defect together. The data are still input-dependent oracle traces; see
the final section of `INVERSION-LOCALIZATION-GATE.md`.

`HIGHER-DISTANCE-MOMENT.md` gives an exact weighted-prefix-area decomposition
for `M_s`, the sum of threshold distance^s over misplaced wires. `M_1` is
inversion; `M_2` and `M_3` offer tighter localization in finite traces. At
depth64 both left/right traces pass the `27/301` radius gate for `s=2,3`.
This is only an input-dependent oracle screen; the all-profile fixed-provider
transfer for the weighted defects remains open.

Uniform U has a conditional227.5 layer count but an observed address-routing
defect under its ideal local split, and its existing small-row B2 bound is
quantitatively inapplicable. The saturated sparse-bottom D2 candidate also has
nominal coefficient227.5, but its depth-200 screen finds a minimum fringe of
`57344/22191` (~2.58) rows at an ordinary mid sender. This rules out relying on
the currently screened fixed-fringe certificates, not on every variable-fringe
provider. A schedule calculation now bounds every sender allocation in any
fixed terminal tail by `m*8^(L+6)`, independent of depth, so tail local-sort
cost is asymptotically harmless. However, the depth-100 physical-scale screen
still has fringe `57344/10221` (~5.62) before a 40-stage tail, below the
currently closed fixed-fringe probability screen at `f=11` (which itself is
not a complete provider theorem); depth150 with the same tail drops to
`57344/15471` (~3.71). Local-bag cleanup also still lacks a global-order
contract. The two fixed-tail witnesses fit `a/c=(105d-279)/2048`, so their
fringe would decay like `1/d` if this phase identity extends; that extension
and the analogous all-`L` family are the next exact recurrence target. See
`D2-SPARSE-BOTTOM-300.md`.
Details: `D2-SPARSE-BOTTOM-300.md`, `UNIFORM-227-CANDIDATE.md`, and
`D2-FRINGE-FACTOR.md`.

Correction to earlier status entries below: the `271/256` role split was
invalid because it treated the previous `botDesc` deficit as zero. The
corrected paper target is `279/256`; finite audits have been updated to check
that weaker bound. Neither target is an all-depth theorem yet.

2026-10-20. Codex (GPT-6), branch `sub300-structural`, isolated worktree
`.claude/worktrees/sub300`, based on main `5f03290`.

Active bounded paper test. No improved coefficient or Lean theorem.
Reuses UB-24's identities and the existing integer D2 flow; no new routing
Lean was written. Read PLAN and REVIEW for the precise oracle relaxation.

Observed results, all (x,y,z)=(2,3,2), native policy, seed0:

| d | exact cutoff C | epsB | epsF | deltaF | root | prefix dominance | result |
|---|---:|---|---|---|---|---|---|
| 8 | 1024 | 0 | 1/16 | 1/8 | exact | no | exact final counts at q/N=1/2,1/3,1/16 |
| 9 | 1024 | 1/100 | 1/16 | 1/8 | exact | no | L1=16 at q/N=1/2 |
| 9 | 1024 | 1/100 | 1/16 | 1/8 | exact | yes | L1=66 at q/N=1/3 |
| 9 | 1024 | 1/100 | 1/16 | 1 | exact | yes | L1=2 at q/N=1/3 and1/16 |
| 10 | 1024 | 1/1000 | 1/16 | 1/8 | exact | yes | sampled1/2,1/3,1/16 pass |
| 10 | 1024 | 3/1000 | 1/16 | 1/8 | exact | yes | L1=46,12 at1/3,1/16 |
| 10 | 1024 | 1/128 | 1/16 | 1/8 | exact | yes | L1=236,100 at1/3,1/16 |
| 11 | 65536 | 1/100 | 1/16 | 1/8 | exact | yes | sampled1/3,1/16 pass |
| 11 | 65536 | 1/100 | 1/2 | 1/16 | exact | yes | sampled1/3,1/16 pass |
| 12 | 65536 | 1/100 | 1/16 | 1/8 | exact | yes | L1=4324,19 wrong final bags at1/3 |
| 12 | 65536 | 9/1000 | 1/16 | 1/8 | exact | yes | L1=3802,18 wrong final bags at1/3 |

The larger cutoff matters: its exact-sort depth is136, still below a
hypothetical234-layer ordinary stage. Thus the C1024 failures did not reject
this larger frontier. The d12 failure now shows that simply increasing the
cutoff to65536 does not close the tested coarse contract either.

For this geometry the leading stage rate is5/4. The nominal q12 three-sort
cost would be234, coefficient292.5, before a valid invariant and provider.
The existing bulk walk table gives approximately0.00935 at q12. There is no
certified fringe provider within that budget; fitting a low-J fringe estimate
is not a construction. Large clipped top bags cannot be charged as small
exact frontiers. The exact initial root is also unpriced.

Recorded witnesses are small lists of nonideal decisions; all other nodes
are ideal. Replay does not call the LP, and verifies local integer bounds,
capacity/zero conservation, final native partition and, where enabled,
every input prefix. It shares code with the oracle, so is not independent
verification. Example:

    python upper-bound/experiments/prefix-flux/replay.py upper-bound/experiments/prefix-flux/monotone-witness.json

The surviving path now has a scaling capacity obstruction:678 wrong ones
enter a wholly-zero native subtree with total future escape at most8192/15.
See CUT-OBSTRUCTION. Raising any fixed cutoff only shifts the same coarse
oracle failure to a larger scale. The9/1000 witness also lies below the
q12 bulk-table value; neither statement supplies a universal provider result.

Verification: exact replay of both d12 witnesses and the d9 monotone witness;
`cut_certificate.py`; ticket validator and git diff check. The existing table
builder now avoids allocating never-active leaves and accepts a finite
horizon. Full old/new tables matched for d3..7, designs U/D2/P (15 cases).
No Lean build or contribution validation: no claimed sorting bound.

Next: derive a capacity-compatible rank-sensitive spill contract for an actual
fixed provider, using the existing tail work first. Do not formalize the current
coarse postcondition interface or infer impossibility for all fixed providers.

## Moderate-tail follow-up

MODERATE-TAIL now derives a reviewed rank-sensitive tail and a centered-ragged
layout avoiding a large padding surcharge. Numerical interval checks at fixed
dyadic witnesses give escape bounds530 and132 at the coarse trace's critical
t4/t5 bags, excluding its1099 and678 choices. The global recurrence and
tiny-rank guarantee remain open; no improved coefficient is claimed.

The oracle's Boolean words now use run-length encoding. Prefix dominance is
checked at all input/output run endpoints, which suffices between endpoints
because the difference is linear. Existing saved traces still replay with
the same decisions and final errors; no arrays proportional to N are needed
for the prefix check.

Source audit identified the next essential gate: the current implementation
interleaves incoming wires in static global-label order. The concatenation
oracle does not model that stronger reachability. See ORDERED-GATE before
doing further recurrence tests. In the faithful ordered model an exact root
must leave no later errors, a useful diagnostic missing from the old harness.
The historical default capacity probe is a concatenation relaxation;
the ordered follow-up below models the actual interleaving.

## Ordered gate and local price follow-up

Ordered static-label mode is now implemented and independently reviewed;
see ORDERED-GATE for controls and limitations. It checks the sorted-root
fixed point and global Hamming nonincrease, and allows errors inside a
threshold-straddling output port. Tests remain adversary samples.

TINY-FRINGE records a reviewed interval-bound refinement retaining the exact
first integer support cap. A thirteen-row point is possible in the paper
bounds only at a very small supported rank fraction. It fails the current
Lean hf16 API guard; the reviewed zero/nonzero-jmax extension and numerical
proof are not formalized. It is not the stronger fringe assumption used in
the current ordered samples.

INFLATED-SCHEDULE records a reviewed constant inflation of the D2 table,
giving exact4096-row rectangles and a large fixed final cleanup charged once.
This removes the repeated small-sort/padding obstruction, not the global
invariant. The `(3,3,2)` fringe-factor note gives an exact two-step allocation
identity: under `g,rho <= 1/256`, ordinary sender ratios are at most `9/8`.
The new `d2_fringe_audit.py` checks the narrowed schedule cases and all these
rational inequalities through depth 100; it found no finite counterexample.
`D2-FRINGE-FACTOR.md` now gives a paper derivation of the all-depth schedule
and `g` induction; a fresh mathematical review found no remaining arithmetic
gap. It is not Lean-checked, and proves only a local allocation/fringe factor.
See [D2-FRINGE-FACTOR.md](D2-FRINGE-FACTOR.md). Next: ordered
spill/profile recurrence and universal D2 native partition; no Lean until the
complete paper gate closes. Important transfer gap: the 8192-row fringe ratio
does not meet existing `NodeGeom`/`TwoRoundSeparatorExists` requirements
(`m>2^42`, `f=0` or even `f>=131040`, with exact divisibility equations), so a
new small-row provider and exact geometry are required.

## Exact compressed flow and first-sort profile gate

Current next-step specification: **PROFILE-GATE.md**. It records a freshly
reviewed stronger local interface for the actual three-sort construction:
prefix dominance over its mandatory first column sort, and shifted sparse
tails above every baseline row. The shared-witness counting overhead is
explicit, including reflected cut coordinates. Global preservation remains
unproved. Reviews: `first_column_review`, `shifted_profile_audit` (GPT-6-luna).

`flow_dag.py` shares identical deficit subtrees instead of enumerating4^d
bags. Reproducible comparison against the existing explicit table matches
17541 active rows at d3..10. At d40 it represents the complete88-stage flow
in29483 states and checks terminal native intervals for every reachable type.
Finite checks through d80 find minimum ordinary fringe ratio1/303, attained
already at d20,t22,level6,a2121,pi14; this is NOT an all-depth geometry proof.

`sparse_probe.py` retains actual wrong-label intervals and tries to preserve
the incoming word whenever its contract allows, rather than sorting every
large output port incidentally. Full d20 tests expose ordered capacity gaps
for remote root errors if the mandatory first sort is omitted; including it
excludes the three sampled gaps. Central and column-aligned initial profiles
also pass the full schedule. See PROFILE-GATE for scope and parameters.
These samples retain the unpriced fringe/bulk assumptions: no sorting bound.

Useful focused commands:

    python upper-bound/experiments/prefix-flux/flow_dag.py --depth 20 --compare-explicit 10
    python upper-bound/experiments/prefix-flux/first_column.py
    python upper-bound/experiments/prefix-flux/sparse_probe.py --horizon 60 --initial outer

The rectangle-to-port frame is checked against `R1Wire`/`R1Exec` and
`PhysicalPack2`: ports are static-order rank intervals, local networks are
presented in that rank order, and physical/semantic whole-row counts agree.
The remaining issue is global transfer, not the rectangular port frame.
`wire_partition_check.py` now checks the stronger discrete routing identity:
each active node's up/down rank slices, plus unchanged inactive bags, partition
every next-stage bag's exact static-wire intervals with neither omissions nor
duplicates. It passed all stages at depths 2--8 for scale 1 and 2 (699,048
bag checks per scale at depth 8). This validates the flow-coordinate mapping
for a later profile model; it adds no comparator constraint or global invariant.
`PROFILE-GATE.md` now gives the exact global defect decomposition into a
cross-bag alignment term plus local prefix defects, and its one-stage bound
when local rank tails are available. `global_prefix_flux.py` checks the
decomposition at every global cut and stage for random Boolean profiles,
including depth 8 at scale 1. This validates the algebra and partition
coordinates only; it does not establish the needed quantitative contraction.
The follow-up finite-cut closure remains modest: depth8/scale4096 uses at
most2,625 local cuts per stage. The ordered `coupled_rank_lp.py` now imposes
global-profile consistency and local prefix dominance at those selected cuts.
At depth6/scale4096, even with root rank-tail bounds and the exact first-column
lower bound at all 4096 full-row cuts, an integral relaxation witness leaves
456,448 wrong keys outside the crossing terminal block. This is not a network
counterexample because unselected local prefixes remain unconstrained; it
shows the finite interface still cannot certify the candidate. See
`PROFILE-GATE.md` for the exact cut counts, witness scope, and next gap.
`rank_recurrence.py` propagates zero-count intervals using the local
one-sided rank-tail bounds, including the required common-witness factor
`m^2` for baselines. At depth7, scale65536 and threshold1/3 it cannot certify
63 terminal blocks as pure. This is a conservative-relaxation failure from
lost correlations, not a counterexample to a fixed core. See PROFILE-GATE for
the exact conditional frame argument and next invariant requirement.

`coupled_rank_lp.py` keeps each node's output prefix profile correlated with
all of its ports and solves one global LP over the D2 horizon. Even with an
exact sorted root, its corrected tail-only contract admits an integral
terminal impurity at d6 (7,884,863 wrong keys total, maximum1,904,413 in one
block). The missing constraint is prefix dominance over the actual local
input profile. The ordered sparse oracle does impose that for selected
input-dependent traces: d12, scale65536, threshold1/3, root-error fraction
10^-6, outer/left/right band profiles all pass with1782 errors confined to
the crossing block. No fixed provider or arbitrary-input root initialization
has been established. See PROFILE-GATE for full scope and commands.

The LP now stores its path constraints sparsely; recoloring and interval
queries avoid repeated scans. First-sort validation:8490 literal comparisons;
recoloring/interval validation:3000 randomized exact comparisons. Historical
monotone trace replay remains valid. No Lean build was needed or run.

The joint profile-weighted MGF screen is recorded in `PROFILE-WEIGHTED-MGF.md`
and implemented in `profile_mgf_dp.py`. The finite nested-subset DP agrees
with direct profile enumeration on a small instance. Its asymptotic variational
rate suggests a possible local-tail gain, but the current tangent calculation
is only a floating diagnostic and is not a certified upper bound. Even a
certified local gain would leave the coupled global transfer and terminal
purity gap open; no coefficient improvement or Lean result follows.

## Uniform-flow 13-bit pivot (2026-10-21)

`UNIFORM-13BIT-CANDIDATE.md` screens the uniform Chvatal flow at `(3,3,2)`.
Fresh-context algebra review verified its role-dependent exact rectangles and
conditional coefficient273, subject to the current-node interpretation of
`native` in the bottom-role numerator. The finite geometry script passes
through depth100. This removes the D2 exact-rectangle obstruction on paper,
but does not establish an all-depth sorter.

The first local probability screen is `uniform_13bit_probability_screen.py`.
For the critical `f=15` role, the current generalized F2 interval envelope
passes only at tested `delta<=10^-12` (with exact E=2 support); it fails at
`10^-11` and above. This remains nonformal, exceeds the current Lean API's
small-f range, and may be too restrictive for global rank-tail transfer. The
next decision gate is to derive the actual rank-fraction requirement from the
global recurrence and compare it with this envelope before investing in a
new provider proof.

Follow-up exact count: `uniform_13bit_geometry.py` now counts positive-fringe
`(time,level)` geometries for which `floor(delta*f*n)=0` at `delta=10^-12`.
Across finite depths3..100 this occurs in25,430 cases, including22,535
`mid` cases. Since the F2 small-rank clause is then restricted to zero
residual mass, this sharply limits the value of the passing interval screen.
It is not a formal impossibility result: large-rank clauses or a stronger
global invariant might still handle these stages. The current actionable gate
is to derive such a transfer or reject this local-provider instantiation.

The generic tail screen `uniform_13bit_tail_screen.py` gives a complementary
finite local bound: for one residual row (`i=1`) at the smallest mid rectangle,
the outward bound allows escape `0.320109612291*n`; for the smallest
`botDesc_small` rectangle it allows `0.184944469439*n`. Applying the same
one-round bound again does not force the residual to zero, since the rounded
mass class remains `i=1`. This does not rule out a different two-round or
rank-sensitive theorem, but the existing moderate-tail interface does not
bridge the zero-support cases.

## Uniform U candidate at conditional 227.5 (2026-10-21)

The current alternate route is `UNIFORM-227-CANDIDATE.md`, using uniform
Chvatal design U with `(x,y,z)=(3,2,2)` and scaled family `N=2^14*8^d`.
Three 13-bit bitonic sorts per stage cost273, and the stage/log rate is5/6,
giving the conditional coefficient227.5. This is a candidate construction
only; no improved upper-bound theorem is established.

Evidence: `uniform_227_geometry.py --depth 100` checks finite exact
rectangles and finds all positive-fringe roles have
`floor(10^-5*f*n)>=1`; `uniform_227_explicit_check.py --depth 7`
cross-checks the actual explicit uniform-U scheduler on 90,202 active-node
instances; `uniform_227_probability_screen.py` passes its interval-arithmetic
F2 envelope at the `1/10000` wrapper budget at every listed fringe size,
including its exact `E=2` term. These checks do not prove all-depth
geometry, a Lean local provider, or global sorting.

The immediate local-provider issue is to replace `F2Pre.hf16`
(`delta*f*16>=1`) with a per-rectangle positive rank-cap premise
`delta*f*n>=1`; the finite scan's minimum value is1.14688. The existing Lean
`F2Pre.hf16` is used to prove `jmax>=1`, but R1/SR theorem hypotheses and the
simultaneous SR/R1/R2 conjunction still need a careful role-by-role audit.
The larger unresolved gate remains the all-depth coupled rank/prefix invariant
through U and terminal purity. Do not begin Lean until the full role-wise
parameter and global-transfer specification has fresh review. See
`UNIFORM-227-PROVIDER-GATE.md` for the role-wise parameters and blockers.

The B2 budget has also been quantified: under the existing union bound, even
at `m=8192`, `n=16`, and the current round-one constant, the B2 error parameter
would need to be about `0.00248` to reach a `1/1000` failure fraction. That
allows about `0.124%` rectangle leakage, roughly 146,000 times the current
target, so this relaxation only helps if a new global invariant proves that
such errors still contract to exact terminal purity.

The exact U routing check now adds a stronger obstacle: with ideal local
rank-ordered splits, depth5 `(3,2,2)` leaves 1,280 wrong-address keys after
the final scheduled stage (worst terminal-node fraction 0.078125); the D2
cut-layout control leaves zero. The witness scales homogeneously to the
candidate's `2^14` wire scale. This is not an actual-network counterexample,
but it rules out proving U by exact address preservation. Before further
provider work, the route needs a validated compensation recurrence or a
D2-like nonuniform flow. Reproduction and scope are in
`UNIFORM-227-ROUTING-OBSTRUCTION.md`.

The current candidate pivot is the D2 cut layout with sparse-bottom
saturation; see `D2-SPARSE-BOTTOM-300.md`. The arithmetic screen checks the
corrected lattice: active allocations/deficits in `m=2^14` units, stored
low/high offsets in `m/2` units, uncapped ordinary quotas in `2m` units, and
ordinary cut fronts on the `m` grid. Send-all allocations need only be in
`m` units. The screen passes at depths 10, 20, 60 and 100. Uncapped
regular-quota divisibility has a short role-wise schedule derivation. The
previous stronger claim that capped ordinary send-alls remain in `2m` units
is false: at depth14, stage26, level12 (`botDesc`), `a=m` and the planned
quota is `14m`. The remaining phase target is that every ordinary sender at scale2 has even
cut fronts. The screen checks this directly through depth150. At scale2,
ordinary unsaturated quotas are divisible by4, so even incoming offsets stay
even after halving; send-all quotas can be odd multiples of2, making descendant
offset tracking necessary. Odd send-alls occur only at `botDesc`/`botRise`
levels and have no later ordinary cut at the same level in the finite scans,
but that does not control odd offsets in child states. A role-wise exact screen
through depth150 finds every positive capped ordinary class is `botDesc`;
positive `topRise` and `mid` allocations always exceed their planned quota.
Once the scale2 parity induction is proved, the physical scale `m=2^14` is an
exact factor 8192 copy. Positive `topRise` and `mid` nodes also never saturate
in the finite scans, though this stronger fact is unproved and unnecessary.
At depth 60,
minimum nonzero quota valuations by role are 20 (topRise), 16 (botDesc), 16
(botRise), and 17 (mid). The candidate's conditional coefficient is262.5;
sorting correctness, shrinking-fringe providers, and the global rank recurrence
remain open. Separately, the generalized exact wire-partition checker passes
the saturated `(3,2,2)` flow at `m=2^14` through depth6 (2,396,744 bag checks).
This validates only finite routing geometry, not the all-depth routing or
sorting claim; details are in `D2-SPARSE-BOTTOM-300.md`.

The scale-2 phase screen directly checks that all ordinary cut fronts stay
even through depth150. It also finds every odd-`m` send-all is `botDesc` or
`botRise`, with no later ordinary cut at that same level. The previous exact
final-two-stage location formula is false: at depth150 there are 4 `botDesc`
classes at `(t,i)=(365,147)`, 18 at `(366,148)`, and 10 `botRise` classes at
`(367,149)`. The no-future-ordinary-cut observation does not by itself control
odd offsets in child states. The depth150 screen also verifies the canonical
boundary-profile floor and transition rule at 360 stages (28 profile types;
358 adjacent transitions), extending those finite checks beyond depth100.

At the boundary `i=omega(t)-2`, address1 has zero parent deficit and
`a/c>=63/64` in 233 tested stages through depth100. The depth30 child profile
was fixed, but depth100 has 16 observed profile types (e.g. `a/c=65/64` at
`d=100,t=94,i=38`). The screen also verifies `a/c>=63/64` for every positive
mid sender through depth100. All 16 boundary profiles dominate the same
coordinatewise floor, which explains the ratio bound for this zero-deficit
family. This suggests an evolving-profile induction; neither the boundary
floor nor the all-mid lower bound is proved.

The index1 boundary-profile check also verifies a compact transition rule
through depth100: an increase of `omega` preserves/increases each profile
coordinate; a decrease resets exactly to the floor. Proving this two-case
rule from the exact cut recurrence is the next local arithmetic goal.

The standard (unsaturated) D2 local gate now has a sharper paper target in
`D2-FRINGE-FACTOR.md`: a role-split two-step estimate `a/c<=271/256`, which
would support the 14-row ragged provider geometry. Exact audits through depth
100 pass the ratio and `g<=1/512` checks; the all-depth schedule/identity
proof is still conditional, and the 273 route's global rank recurrence stays
open. This is distinct from the sparse-bottom 262.5 candidate below, whose
observed fringe shrinks and whose provider gate is harder.

An exact two-step state-triple audit now verifies the allocation identity for
every mid sender through depth100 at both scale2 and the physical `2^14` row
scale. It confirms `G_t<=G_{t-2}` and the finite `a/c>=63/64` bound, but also
shows why quota monotonicity alone cannot prove it: some `botDesc` parents and
children are positively capped, and their normalized child-quota sum can be
zero. The needed invariant must couple the two-stage deficit drop with the
actual quotas; see `D2-SPARSE-BOTTOM-300.md` and
`d2_two_step_audit.py`.

The physical-scale audit now additionally verifies `G_j(current)=G_j(cut)+pi_j`
for each child in every aligned mid-sender triple: all 4,733 checks at depth30
and all 225,619 at depth100 pass. This gives an exact finite split of each
half-profile into the prior clipped-tail debt and four fresh child quotas;
proving their coupled lower bounds remains open. The half-profile inequalities
themselves pass on all 219,845 distinct mid states through depth100, with
minimum slack zero; the componentwise strengthening still fails.

The scale-2 extension to depth150 checks 802,659 aligned mid-sender triples
and 787,649 distinct mid states. The two-step identity, child-deficit update,
`G_t<=G_{t-2}`, and `a/C>=63/64` all pass; both half-profile inequalities
still hold with zero slack. The componentwise strengthening fails with minimum
margin `-1009/65536`. This is finite evidence only; no all-depth induction has
been found.

## Ragged D2 local F2 parameter point (2026-10-21)

For the explicit `n=8307` ragged 13-bit sender (`f=14` or `15`), a shifted-cut
screen now passes both F2 orientations at `ÃŽÂ´=18/(fÃ‚Â·8307)`: use
`(g1,g2,c,b,J)=(7,9,1/3,6/5,1)` for `f=14` and
`(8,10,1/3,6/5,1)` for `f=15`. The closed interval bounds give
`ln(2P1),ln(2P2)=(-8.73133,-6.97134)` and
`(-9.04436,-6.97134)`, respectively. They pass the `1/1000` budgets,
including the generic `E=2` terms, and satisfy `c+1/2Ã¢â€°Â¤b`; the old
`deltaÃ¢â€°Â¤10^-12` result was specific to the previous cut choices. Independent
fresh reviews checked the previous exact-per-E point; these refined
closed-form parameters are queued for fresh review.

This is a numerical certificate candidate, not Lean. The closed envelope
passes, but `F2Pre.hf16` fails because
`ÃŽÂ´ fÃ‚Â·16=288/8307<1` even though `floor(ÃŽÂ´ fÃ‚Â·8307)=18`. Only two Lean proof
sites consume `hf16`, so a local-dimension variant is plausible. The global
fixed-ragged-mask port/provider theorem and the 273-stage global transfer are
still open. Details and reproducer: `RAGGED-13BIT-PROVIDER.md` and
`ragged_provider_probability_screen.py`.

Correction after fresh review: the closed-form screen is confirmed, with P2's
log margin only about `0.0636` below `ln(1/1000)`. It does not satisfy the
existing strong per-event Lean guards `R1aNumd`/`R1bNumd`; a direct aggregate
R1 sum proof is needed. The local rank gap is separate: at the actual
dimension `n=8307`, the candidates have `jmax=18`. A scratch local-rank
lemma is being added to remove the irrelevant uniform `hf16` assumption. The
R2 aggregate sums, fixed-mask provider, and global transfer remain unproved.

## Equalized ragged sender geometry (2026-10-22)

`RAGGED-ALL-SENDERS-GATE.md` records an exact shape construction for each
positive-up ordinary D2 sender. Through depth100 at scale8192, the compressed
flow screen found 19,606 distinct `(allocation,up)` pairs, all realized with
fringe widths at least13 and column heights at most8192. The maximum observed
cumulative-cut mismatch from a common row cut was16 cells per column.

A paper median-cut estimate improves the deterministic transfer bound to
`33n/2`: write each bulk width as one of two consecutive integers and each
column height as one of two values differing by2. For `d=11/2500` and local
`epsB=17/2000`, the B2 leakage plus this mismatch fits in the local cut budget
with a small positive margin. The round-two exponent screen at `m=8192,n=16`
has log failure fraction about `-132.7` under `E1=371/10^8`. These are
research screens and a paper inequality, not a provider theorem.

Next gate: prove from the role formulas that the equalized integer profile has
`f_j>=13` for every active sender (including startup), then verify the
relaxed `epsB` in the global rank-profile recurrence. The first-round event,
F2 for varying fringe widths, and fixed-mask extraction also remain open.

Follow-up screen: the F2 tail condition need only use the minimum fringe
`f_*` of a profile. Its uniform non-fringe region contains each column's
ragged bulk, so the rank bound transfers without a geometric error term. The
depth30 profile scan has `f_*=14` minimum; the least column counts for
`f_*=14,15,16` are `8195,4157,4096`. The shifted-cut numerical F2 envelope
passes at budgets `1/1000` for `(14,8195)` and `1/10` for `(15,4157)` and
`(16,4096)`. This leaves the small-dimension Lean guard, the all-depth
`f_*>=14` proof, and the combined probability choice open. See
`RAGGED-ALL-SENDERS-GATE.md`.

The constrained waterfill geometry is now stated with a 13-row floor in
`RAGGED-ALL-SENDERS-GATE.md`, correcting the earlier 14-row argument that
relied on the superseded `271/256` sender factor. Conditional on the corrected
`279/256` factor and schedule capacity floors, the feasible-profile inequality
and median-cut mismatch bound close on paper; the depth-100 screen passes all
19,606 distinct sender pairs. This remains conditional geometry, not a provider
or sorting theorem.

The bridge additionally checks `semanticExec2_comp_monotone`, allowing any
monotone Boolean threshold to be transported through the actual semantic
two-round network. The fixed-core mass identity
`fullHeightTwoShuffle_total` is also checked. The remaining local rank step is
to identify the output profile mass with the input's threshold count; then
tile-local rank intervals must still be reconciled with the global D2 flow
state.

The standard `(3,3,2)` exact two-step identity is independently audited
against `FlowDAG`: depth100 covers 206,594 ordinary positive-up senders, with
all identity and role checks passing. The corrected role split targets
`a/c<=279/256` using `g<=1/512`; exact finite audits pass, but the all-depth
noncrossing/schedule proof remains conditional. The global rank recurrence,
provider probability, root initialization, and terminal correctness also
remain open. See `D2-FRINGE-FACTOR.md` and `RAGGED-ALL-SENDERS-GATE.md`.

## Actual stage-five bridge (2026-10-23)

The run-aware Lean development now proves the saturated-aware tree invariant
through the complete fifth scheduled stage for dimensions at least nine.
`d2FlowCandidateStage4_local_levelThree_cap` turns the actual stage-four
level-two cut gate into the normalized stage-five child cap. The stage-two
first-sender subtree has native level-four reserves; stage three preserves them
through its level-three bot-rise, and stage four preserves them through the
inactive levels three and four. Since the stage-five cap is strictly below the
native level-three size, the invariant also forces balanced endpoints. These
facts yield actual stage-five level-three gates, then the whole-tree stage-five
input predicate and invariant preservation. The focused Lean check passes, and
`D2ScheduleReserve.lean` contains no `sorry` or `admit`.

This closes the bootstrap bridge through stage five; it does not establish the
candidate's repeating schedule invariant. The all-depth `279/256` sender
factor and noncrossing argument, provider/rank transfer, root/terminal
contracts, and final sorting theorem remain open. The coefficient `273` is
still conditional and is not a proved upper bound.

The first repeating transition is now fully checked in
`D2ScheduleReserve.lean`. Stage-six frontier roles and capacity ratios are
proved; `d2FlowCandidateStage6_actual_mid_state` derives the midpoint cap and
child reserves from the actual stage-five cuts; the level-four bot-rise nodes
are balanced by the ordinary-cut root identity; and the inactive tail and
root/level-one gates are packaged in `d2FlowCandidateStage6_actual_inputs`.
`d2FlowCandidateStage6_preserves_inv` composes these with the generic local
theorem, extending the actual whole-tree invariant through six scheduled
stages for all `d>=9`. The all-depth reserve/cap recurrence and `279/256`
sender bound remain unproved, as do provider/rank transfer and the root,
terminal, and sorting contracts. The coefficient273 is still conditional.
The stage-seven frontier classifier now confirms the next scheduled pair is
again level-one top-rise/level-three bottom-descending, with level five
inactive; proving its actual gates from the stage-six output is the next
bootstrap test.

2026-10-23 update: Stage 8 is now fully checked in `D2ScheduleReserve.lean`
for `d>=10`. The actual level-four `botDesc` gate follows from transported
native reserves; the actual level-two `mid` gate follows from the stage-seven
top-rise cap and bottom-descending quota increments. The root remains at zero
through stages 0Ã¢â‚¬â€œ7 because each active root stage in this prefix is
top-descending; run-stage-8 invariant supplies its balance condition. These
facts assemble `d2FlowCandidateStage8_actual_inputs`, and
`d2FlowCandidateStage8_preserves_inv` carries the whole-tree invariant through
run stage 9. Verification: `lake env lean
../prefix-flux/D2ScheduleReserve.lean` from `upper-bound/experiments/runaware`
completed successfully. This closes only the finite Stage 8 bootstrap; the
all-depth reserve/cap recurrence, provider/rank transfer, later-stage
invariant, terminal contract, and sorting theorem remain open. Coefficient
273 remains conditional and is not a proved upper bound.

2026-10-23 update: Stage 9 is now closed as a concrete run transition for
`d>=11`. In addition to the root reset and level-one top-rise gate, the actual
level-five bot-rise balance/tail, inactive level-four recursion, and actual
level-three mid gate are proved. `d2FlowCandidateStage9_actual_inputs` builds
the full root predicate, and `d2FlowCandidateStage9_preserves_inv` transports
the invariant through run stage 10. The focused command
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` from
`upper-bound/experiments/runaware` passes. This advances only the finite
bootstrap: the all-depth sender-factor recurrence, provider/rank transfer,
later-stage invariant, terminal contract, and sorting theorem remain open.
Coefficient 273 is still conditional.

The stage-ten frontier is also kernel checked for `d>=11`: levels 0/2/4 have
roles topDesc/mid/botDesc, with level 6 inactive. Its actual gates are the
next bootstrap step; see `D2-STAGE9-BRIDGE.md`.

The finite `d2_reachable_reserve_audit.py` also passes at depths 30 and 60
(4,660 and 42,128 ordinary sender states checked). This cross-check covers
stage ten in the concrete DAG, but does not establish the all-depth recurrence.

2026-10-23 verification: a full focused check of the current
`D2ScheduleReserve.lean` completed successfully with
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` from
`upper-bound/experiments/runaware` (exit 0). The next finite bridge is to prove
Stage 10's actual level-two mid gate, then assemble the root input predicate
and preserve the invariant through that run stage. Separately, a possible
fallback is to revisit Chvatal's uniform per-node outsider allowance with
depth- or mass-dependent budgets and a global charging potential; this is a
research lead only, not an established relaxation of the all-input invariant.

The first Stage 10 endpoint bridge is now kernel checked:
`d2FlowCandidateStage10_levelThree_endpoint_reserve` proves that every
level-three child in the stage-ten input tree has deficit at least the reserve
required by a level-two mid sender. The proof transports the stage-nine
level-three mid quota through the actual descendant-first recursive stage and
uses the exact capacity ratio. The full focused Lean check passes after this
addition. The level-two sender-cap/balance transfer, allocation bound, full
Stage 10 input predicate, and invariant preservation remain open.

Correction: those Stage 10 obligations have now been closed in
`D2ScheduleReserve.lean`. `d2FlowCandidateStage10_levelTwo_inherited_state`
transfers the level-one top-rise child bound with balanced endpoints;
`d2FlowCandidateStage10_actual_levelTwo_inputs` composes that with the
level-three reserves and level-four gates. The root remains empty through
Stage 9, yielding `d2FlowCandidateStage10_actual_inputs`, and
`d2FlowCandidateStage10_preserves_inv` proves the whole-tree invariant through
run stage 11 for every `d>=11`. The full focused Lean check passes. This is
still only a finite bootstrap step: the all-depth reserve/cap induction, the
global provider/rank transfer, terminal contract, and sorting theorem remain
open; coefficient 273 remains conditional.

2026-10-23 research lead: the exceptional `botRise`-child branch may permit a
more tolerant per-node deficit budget than `g<=1/512`. In the exact unsaturated
`(3,3,2)` `FlowDAG` scan at depth 50 (row scale `2^13`), all 1,644 exceptional
ordinary senders had aggregate intermediate-child quota sum at most
`241/8192`, with equality in 44 states. The equality profile is
`[49/16384, 1/256, ..., 1/256, 49/16384]` (six middle terms). The generic
per-child bound `rho<=1/256` only gives `1/32=256/8192`. Replacing that coarse
sum by `241/8192` in the exceptional factor calculation would allow
`g_old<=23/4096` while retaining `a/c<=279/256`:
`16*(23/4096)+16*(15/4096)+32*(241/8192)=279/256`.
The regular branch already tolerates `g_old<=23/4096`; local endpoint and
child-cap arithmetic also appears compatible with that cap. This is only a
finite-flow observation and an algebraic target, not yet a universal theorem.
The structural source of the aggregate is the strong `botDesc` parent visit:
the two end-child blocks are `49*c_old/8192-low/high`, while the six middle
blocks are `c_old/128`. With `c_old=16*c_now` and the intermediate child
capacity `32*c_now`, the endpoint terms normalize to at most `49/16384` and
the middle terms to `1/256`. At the following `botRise`, each child's whole
bag is its up-port. The schedule forces this strong-parent configuration in
the exceptional case.

The arithmetic interfaces are kernel checked in `D2ScheduleReserve.lean`:
`d2_botRise_child_quota_sum_of_endpoint_caps` and
`d2_botRise_child_quota_sum_of_strong_parent_blocks` establish the aggregate;
`d2_two_step_sender_factor_279_of_tolerant_budget` then gives `a/c<=279/256`
with `g_old<=23/4096`. The same focused check verifies that this relaxed cap
fits the `c/128` endpoint reserves, preserves the ordinary child-deficit
recurrence, keeps the exact two-endpoint/zero-interior ordinary cut shape, and
still proves noncrossing under looser current-deficit
allowances (`7/128` for an ordinary predecessor and `15/256` after `botRise`).
`d2FlowStage_regular_child_profile_tolerant` now lifts the exact cut profile
to the concrete recursive tree transition under these relaxed hypotheses.
The concrete transition also has a new adapter lemma,
`d2FlowStage_botRise_actual_port_of_saturated_children`, identifying the
up-port as the saturated child total minus the root deficit written by its
parent. The arbitrary-depth projection is now packaged by
`d2FlowTreeRun_path_as_history` and instantiated for the candidate run by
`d2FlowCandidateRun_path_as_history`; the focused Lean check passes after
adding these theorems. Existing `botRise_children_parent_trace_native`
already proves the schedule-side native-history fact, while
`d2FlowTreeRun_child_trace` gives the exact child trace for any such path
history. The composition gap is now closed at the interface level:
`d2FlowTreePathContext` packages the selected subtree's effective level and
ancestor-overwrite callback, `d2FlowTreePathHistory_eq_context_run` identifies
its history with a generic local run, and
`d2FlowTreePathHistory_child_trace` gives the exact trace for one more edge
after any path prefix. The focused `lake env lean
../prefix-flux/D2ScheduleReserve.lean` check passes after these additions.
What remains is to instantiate the relaxed cut profile from actual all-depth
candidate gates, derive the saturated grandchild ports, and feed their quotas
into the sharper schedule factor. The coupled reserve/cap induction itself
is still open; these interfaces do not yet prove an all-depth invariant.

2026-10-23 tolerance follow-up: `d2_deficit_tolerance_screen.py` now measures
the actual normalized parent deficit `G/c` on every reachable active ordinary
sender, separately checking quota and endpoint reserves. At scale 8192, the
maximum over all senders at depths 60 and 100 is exactly `15/8192` (about
0.0018311), while the current `1/512 = 16/8192` gate is never violated; every
audited sender passes the other local gates. Depth 30 has a slightly smaller
maximum. This is evidence that the current *finite reachable traces* have
slack, not an all-depth bound. It supports testing a looser invariant, but
doesn't by itself justify increasing the cap: the coupled induction must show
that the slack persists under arbitrary future transitions. The more ambitious
variant is a nonuniform, depth- or mass-dependent outsider allowance with a
global charging potential, so local exceptional branches can spend slack
without multiplying a worst-case cap at every level. Focused runs used
`python d2_deficit_tolerance_screen.py --depth 30 --scale 8192`, and likewise
at depths 60 and 100.

The nonuniform-budget idea now also has a kernel-checked scalar interface in
`D2ScheduleReserve.lean`. `d2_deficit_bound_by_outsider_potential` proves that
if a pathwise normalized deficit obeys `g[n+1] <= g[n]/2 + rho[n]/4`, then
`g[n] <= g[0]/2^n + P[n]`, where `P[n+1] = P[n]/2 + rho[n]/4` is the exact
geometrically weighted history of outsider errors. Under a uniform
`rho[n] <= R`, `d2_outsider_potential_le_half` recovers the limiting allowance
`R/2`; a nonuniform schedule can spend larger errors early, provided this
weighted potential remains within the target reserve. This is a reusable
pathwise inequality, not yet an instantiation for all D2 roles or all nodes.
The role audit showed that ordinary parent cuts overwrite a child, so the
pure contraction recurrence is insufficient by itself. The kernel-checked
`d2DeficitEnvelopeWithCuts` and
`d2_deficit_bound_by_switched_cut_envelope` now model the two mutually
exclusive transitions directly: either contract the current child budget and
charge its port, or reset to a separately bounded parent-cut value. The
uniform-cap lemma `d2_deficit_envelope_uniform_cap` shows that a cap `B` is
preserved when the port branch fits (`R/2 <= B`) and every cut reset fits
(`C <= B`). This avoids charging a reset additively on top of the child's
old budget. The concrete endpoint-reset inequality is now kernel checked:
`d2_normalized_left_cut_le_parent_budget` and its right-end analogue bound the
actual cut value divided by the child's next capacity `2*c` by
`g_parent/2 + rho_parent/4`; `d2_normalized_endpoint_cuts_fit_budget` then
shows these resets fit `B` whenever `g_parent<=B`, `rho_parent<=R`, and
`R/2<=B`. Thus the local normalization and ordinary-cut arithmetic are
closed. What remains is to supply these parent bounds and endpoint reserves
uniformly at every actual sender, handle the `botRise` self-update trace and
`topDesc` zero reset in the same all-depth induction, and connect the result
to the global rank/terminal contract. The focused Lean check passes after
these additions.

2026-10-23 tolerant invariant integration: `d2FlowStageInvInputsTolerant`
now packages the `23/4096` sender cap with the existing allocation, quota,
parity, and endpoint-reserve gates. The strict-to-tolerant adapter
`d2FlowStageInvInputs_tolerant_of_strict` allows earlier checked bootstrap
gates to feed this interface. The actual ordinary child cut profile now
propagates the tolerant cap through one recursive stage via
`d2FlowStage_regular_child_tolerant_g_bound_of_reserves` and its input adapter;
`d2FlowStage_regular_node_inv_of_tolerant_reserves` and
`d2FlowStage_preserves_inv_of_tolerant_inputs` establish whole-tree native
invariant preservation under the relaxed budget. Stage 10's preservation
proof has been routed through the tolerant preservation theorem as a concrete
check; its actual input gate is still supplied by the stricter existing Stage
10 bridge. The full focused Lean check passes. This integrates the tolerance
into the local recursive invariant but does not yet derive tolerant actual
input gates inductively for unbounded schedule stages.

Stage 11 schedule bridge: the kernel-checked frontier theorems now split the
startup case explicitly. For `d>=12`, active levels 1/3/5 have roles
topRise/mid/botDesc, with level 7 inactive; at `d=11`, only level 1 changes
to topDesc. The exact capacity scaling
`d2FlowCandidateCapacity_succ_level_next_stage` proves
`cap(d,i+1,t+1)=2*cap(d,i,t)` whenever the exponent is in range, so the new
tolerant child bound transfers directly to the next-level Stage 11 sender
cap. The focused Lean check passes. Stage 11's actual endpoint reserves,
allocation gates, and full recursive input predicate remain to be derived.

2026-10-23 Stage 11 level-six reserve bridge: `d2FlowStage_botRise_child_root_deficit`
proves that a bottom-rise sender preserves each child-root deficit when the
next level is inactive. This transports the stage-eight native level-six
reserves through the stage-nine bottom-rise and the stage-ten inactive
level-five frontier. The new `d2FlowCandidateStage9_actual_levelSix_native`
and `d2FlowCandidateStage10_actual_levelSix_native` theorems kernel-check for
all depths `depth+6` with `depth>=5`. Thus the level-six endpoint-reserve
input for the Stage 11 level-five bot-descending sender is now closed. The
remaining Stage 11 level-five obligations are the sender cap/balance,
quota/allocation gate, then the level-three and level-one gates and full
recursive stage preservation.

Next structural follow-up: test whether the Chvatal-style per-node outsider
allowances can be safely increased or redistributed. The existing tolerant
`23/4096` gate changes the local invariant interface, but does not by itself
change how outsider budgets are charged through the whole tree. A viable
redesign must prove a global charging rule (including repeated sender visits)
and preserve the terminal exact-count contract; compare mass-sensitive or
shared-budget accounting against the current fixed per-node schedule after
closing the Stage 11 reserve bridge.

Stage 11 level-five gate: `d2FlowCandidateStage11_actual_levelFive_inputs`
now supplies the complete strict local input predicate at every actual
level-five sender for tree depth `depth+6`, `depth>=6`. It transports the
Stage 10 level-four cap and balance through the actual cut, uses the checked
native level-six reserves at both endpoints, and closes quota/allocation with
the `8 + 15 <= 32` normalized boundary-mass estimate. The focused full-file
Lean check completed without diagnostics. The level-three mid and level-one
top gates, then the complete Stage 11 induction and terminal exact-count
contract, remain open; this is not yet a sorting-bound proof.

Stage 11 level-three mid gate: `d2FlowCandidateStage11_actual_levelThree_inputs`
now closes the actual level-three sender input predicate for depth `depth+6`,
`depth>=6`. It carries the Stage 10 level-two cap/balance through the actual
cut, uses the established level-five bot-descending gate and native level-four
reserves, and proves the endpoint reserve and allocation inequalities. The
focused `lake env lean ../prefix-flux/D2ScheduleReserve.lean` check from
`upper-bound/experiments/runaware` completed with exit code 0. Stage 11's
At this point the level-one top gate and full Stage 11 preservation remained
open; the next entry records their subsequent closure.

Stage 11 closure (depth `depth+6`, `depth>=6`):
`d2FlowCandidateStage11_actual_levelOne_inputs` proves the actual top-rise
gate using the Stage 10 level-two mid quota, with projection through the
inactive Stage 10 level one. `d2FlowCandidateStage11_actual_inputs` assembles
the complete strict recursive input contract, and
`d2FlowCandidateStage11_preserves_inv` carries the saturated-aware tree
invariant through run stage 12. The focused `lake env lean
../prefix-flux/D2ScheduleReserve.lean` command from
`upper-bound/experiments/runaware` passes with exit code 0. This closes the
finite Stage 11 transition only; the later-stage induction, global
rank/inversion recurrence, terminal exact-count contract, and sub-300 sorting
bound remain unproved. The next decisive research task is an adversarial test
of the global recurrence, since another finite stage bridge cannot establish
that it contracts. If that gate passes, investigate a globally charged
mass-sensitive outsider budget; the local `23/4096` tolerance alone does not
enlarge the proved all-depth allowance.

2026-10-23 finite adversarial coupled-profile stress test: repaired two
model-indexing issues in `coupled_rank_lp.py` before interpreting results.
Zero-allocation active children are omitted from the sparse `H` variable set,
so their transfer contribution must be zero rather than an `H` lookup; and
the configured `row_count` must be passed to both calls of `prefix_interval`.
With exact sorted root profile, all active row-boundary cuts, propagated
13-row tail constraints, and a per-sender aggregate full-row defect cap of
`17/2000`, the maximizing finite LP/MILP relaxation has optimal terminal
wrong mass zero at depths 5 through 9 (scale 1024, row grid 32, threshold
1/3, parameters (2,3,2)). Depth 9 covers 11 active transitions and 1023
terminal blocks. A depth-8 rerun also found zero deviation at every one of
its 11,642--14,826 represented global cuts per stage. Critical limitation:
these were exact-sorted-root regression controls, so they do not test the
adversarial recurrence from a nontrivial rank profile; the scalar screen's
unresolved-block count is irrelevant in this fixed-point case. The sorted
witness satisfies all equalities, inequalities, and variable bounds, but
that is only a model consistency check. These runs give no evidence yet that
the coupled recurrence contracts errors from a genuine root defect, and do
not prove the local 0.85% defect/tail providers or an all-depth invariant.
The 4096-row depth-6 attempt timed out; the 32-row depth-9 model solved
optimally (about 1.6 million variables, so larger depths will need a more
compact invariant or constraint generation).

Finite nonzero-root follow-up: with only `root_error=1` at selected cuts, the
integer depth-5 relaxation admits terminal wrong mass 2. This is a witness to
the insufficiency of that pointwise profile contract, not to the comparator
network; such a one-unit rank defect can span a long interval and need not
have small inversion count.

Exact-inversion correction and follow-up: the first inversion-cap MILPs were
invalid because a special-case root-output bound forced the root's output to
be sorted. That shortcut is now disabled whenever a root inversion cap is
supplied. To avoid all `N` root variables, the model uses the exact
localization lemma: if `Inv<=I`, every nonzero prefix defect lies in
`[q-I,q+I+1)`. It includes every cut in this band, fixes represented cuts
outside it to the ideal profile, and constrains the exact inversion area in
the band. This is an overapproximation of all true `Inv<=I` roots.

For the 273 candidate `(3,3,2)`, with scale `8192` and local row count
`8192`, depth 5 has `N=2^28` and depth 6 has `N=2^31`; both have four
transitions. The fully integral models optimize worst terminal wrong mass to
zero for every root with `Inv<=3` at depth 5, `Inv<=5` at depth 5, and
`Inv<=6` at depth 6. `N^(27/301)` is about `5.7` and `6.9` at those sizes.
The depth-5 exact cut closure has only about 665 profiles per early stage.
The global profile is already exact after the first transition in both runs.
At depth 3 and scale 32, the same candidate model has zero terminal error
for `Inv<=3`, but at `Inv=100` it admits one terminal wrong key, showing a
finite threshold rather than unconditional sorting. At depth 7 and scale 32
(`N=2^26`, seven transitions), the continuous LP relaxation has optimum zero
for `Inv<=5` (`N^(27/301)` is about 5.0). Its separate all-integer HiGHS run
reported infeasible despite the sorted witness satisfying all linear
constraints and integrality; treat that MILP status as a solver anomaly. The
candidate depth-7 model at actual scale/row count `8192` was canceled after
over six minutes and about 3.4 GB memory, with no result.

These are finite checks of the abstract `prefix_interval`/port-transfer
relaxation, not checks of the fixed ragged 13-bit sorter/provider. They do
not provide the required arbitrary-input prefix-stage initialization or an
all-depth recurrence. The immediate proof target is still to initialize
`Inv<=N^theta` from the fixed priced prefix stage and prove the weighted
transfer uniformly; Lean routing should wait for that paper invariant and
the corresponding fixed-provider bounds.

UB-40 translation gate, 2026-10-24: its multiplier `T` scales the Chvatal
separator's local `eps_B` allowance; it is not the D2 sender-deficit ratio
`G/c`. The finite D2 reserve screen was extended to depth160 at scale8192
(893,061 reachable states; 858,865 active ordinary sender instances checked).
The largest active ordinary-sender ratio was
`G/c = 0.0018310546875` (stage350, level118, `botDesc`), below `1/512`, and
every checked sender instance passed the existing quota and endpoint reserve
tests. This is finite evidence, not an all-depth bound.

There is also a direct geometry limit on a naive D2 tolerance transfer. With
the current quota cap `pi<=c/256` and endpoint reserve `U_1>=c/128`, front
containment follows from `L+pi/2<=G+c/512<=U_1`. Thus this proof interface
allows at most `G<=3c/512` before the current front-fit argument breaks,
only six times the existing `c/512` deficit allowance. UB-40's `T>=36`
cannot be obtained by merely multiplying the D2 `G/c` cap while preserving
the same quota and endpoint reserve. A periodic D2 route needs a new
phase-dependent invariant or a refresh that changes those geometric
reserves; the old `screen.py` cost remains conditional on such a distinct
restoration theorem. Reproduce the finite audit with
`python upper-bound/experiments/prefix-flux/d2_deficit_tolerance_screen.py
--depth 160 --scale 8192 --params 3 3 2`.

2026-10-24 distance-tail / UB-40 follow-up:

`cert_walk_n.py tail` at exact row height 8192 certifies the outward profile
caps recorded in `PROFILE-GATE.md`: margins 64,128,256,512,1024,2048 have
caps 103/10000, 78/10000, 47/10000, 25/10000, 12/10000, 61/100000. A new
`--distance-tail-profile` mode adds the implied one-sided local defect cap
only when the scalar reachable zero-mass interval is separated from a full
row cut. It adds no per-rank selector binaries. `LLM-helpers/tail_profile_cert.py`
quietly reruns these interval certificates.

The candidate-scale gate at depth5, scale8192, row_count8192, parameters
(3,3,2) was narrowed to exact D2 port cuts and a 64-row-stride root tail.
It has 11,219 variables, 8,221 equalities, and 23,941 inequalities; its sorted
witness has zero equality, inequality, and bounds residual. HiGHS returned
`Unknown / primal Basic` without an optimizer point. The same status occurs
with no distance-tail constraints, with a longer limit, and with dual-simplex,
so this run does not test whether the profile contracts. Full row closure was
too expensive to construct. The smaller screen remains unresolved pending a
solver that can return an optimum for this model.

UB-40's `screen.py` already has the periodic cost formula, but its old
Chvatal invariant model returns no feasible point at (3,3,2), even with its
tolerance multiplier raised through 1000; it is not directly reusable for
the D2 quota/reserve invariant. Cost-only arithmetic for 23 stages of depth
273 plus one 24-row three-sort refresh of depth900 is 299.125 per stage, but
does not prove restoration. A refresh can reduce local defects while global
prefix alignment `A_t(r)` persists, so a D2 period map must contract that
alignment as well as refresh the local tail. No sub-300 proof follows yet.

Small distance-profile check (depth2, row height8192): with the same
`(3,3,2)` flow, scale8192, threshold1/3, ordered prefixes, root-tail
initialization, and 64-row sampled cuts, the LP solves optimally. Without a
distance profile it allows8,980 total terminal wrong keys; adding the six
certified outward caps above adds 180 inequalities and lowers this to 6,390.0192.
Requiring all model count variables integral solves optimally at 6,390 wrong
keys (zero integrality residual). This confirms that the profile constraints
have a real effect in a small exact-count instance, but they do not stop global
misalignment. The integer model is still a relaxation of the network trace,
only two transitions deep, and has no periodic precise refresh; it is not
evidence for or against UB-40's restoration claim. The candidate-scale depth5
gate above remains unresolved. Reproduce the integral screen with
`coupled_rank_lp.py --depth 2 --scale 8192 --threshold 1/3 --ordered-prefix
--root-tail --row-stride 64 --params 3 3 2 --row-bits 13 --integer
--distance-tail-profile 64=103/10000,128=78/10000,256=47/10000,512=25/10000,1024=12/10000,2048=61/100000`.

An ideal-refresh diagnostic was added to the same model. The option
`--exact-refresh-stage t` imposes `Y(s)=min(H,s)` at every represented local
prefix of each active bag on transition `t`, using exact binary selectors. For
the preceding depth2 instance, setting `t=1` makes the final local profiles
perfectly sorted (the sorted-path witness passes all constraints), and the
within-bag defect becomes 0. Nevertheless the cross-bag alignment remains 2,682
and the relaxation still admits 5,094 terminal wrong keys. This makes the
structural issue explicit: even an ideal local refresh at the end of the
period does not by itself restore global rank alignment. It is a two-transition
selected-cut relaxation, not a network counterexample or an all-depth
obstruction; the necessary UB-40 deliverable is a refresh map that also
contracts alignment. Reproduce with
`coupled_rank_lp.py --depth 2 --scale 8192 --threshold 1/3 --ordered-prefix
--root-tail --row-stride 64 --params 3 3 2 --row-bits 13 --exact-refresh-stage 1`.

The same ideal-refresh diagnostic was extended to depth5, which has four
transitions: `--exact-refresh-stage 1` followed by two ordinary transitions.
At scale8192 and row stride256 the MILP solves optimally (11,868 variables,
649 refresh selectors). Its post-refresh trace has cross-bag alignment
1,182,710, which rises to1,313,782 by the end; the terminal objective is
2,493,898 wrong keys. The sorted-path witness passes. The matched no-refresh
LP at the same scale and stride returns HiGHS `Unknown / primal Basic` under
both the default and interior-point methods, so this is not a quantitative
comparison of the refresh's benefit. It does
show that an ideal sender-local refresh plus two cheap transitions still
admits substantial alignment in this selected-cut relaxation. The paper
obligation is to bound the full sender-to-receiver period map for `A_t(r)`;
restoring the sender profiles alone does not provide that bound. Reproduce
with `coupled_rank_lp.py --depth 5 --scale 8192 --threshold 1/3
--ordered-prefix --root-tail --row-stride 256 --params 3 3 2 --row-bits 13
--time-limit 120 --exact-refresh-stage 1`.

Follow-up placement test (2026-10-24): moved the same optimistic local refresh
to the end of the four-transition window, `--exact-refresh-stage 3`. HiGHS
solved the 11,339-variable MILP to optimality (zero MIP gap; max equality
residual `1.2e-7`, inequality residual `1.5e-6`, bounds/integrality residual
below `6e-8`). It still admits 4,261,663 terminal wrong keys, with a largest
terminal block error of 1,410,691. At the final snapshot the cross-bag
alignment is 2,590,807 and the represented within-bag defect is 319,864;
63 terminal blocks remain non-pure. This refresh is an optimistic cut-level
constraint on represented prefixes of active bags, not a priced network and
not a concrete input. It confirms that merely placing the refresh at the
period boundary does not restore the global contract in this relaxation.
Reproduce with the same command above, replacing
`--exact-refresh-stage 1` by `--exact-refresh-stage 3`.

Alignment-cap follow-up (2026-10-24): added `--refresh-alignment-cap A`, which
constrains `q - sum_B min(H_B, P_B) <= A` at the snapshot immediately after
the selected exact-local-refresh stage. The `M_B <= H_B,P_B` formulation is
an exact feasibility encoding of this scalar threshold-cut condition; it does
not constrain other cuts or claim a realizable reset. At candidate scale,
using `--exact-refresh-stage 1 --refresh-alignment-cap 0` solves optimally
(11,891 variables, zero MIP gap; sorted-path witness passes, max inequality
residual `9.6e-7`). At snapshot 2, alignment is exactly zero, but total prefix
defect is still 131,072, entirely within-bag. After two ordinary transitions
the total defect remains 131,072 and has shifted entirely into cross-bag
alignment. The terminal objective is 262,144 wrong keys in this fractional,
rounded-infeasible relaxation. Thus an alignment-only boundary condition
does not suffice: the period map must control the local defect and its
conversion into alignment together. This is still not a network
counterexample. Reproduce with
`coupled_rank_lp.py --depth 5 --scale 8192 --threshold 1/3 --ordered-prefix
--root-tail --row-stride 256 --params 3 3 2 --row-bits 13 --time-limit 120
--exact-refresh-stage 1 --refresh-alignment-cap 0`.

The 13-row F2 local-dimension bridge now proves the SR (small-rank) failure
bound uniformly for every column count `n>=3832` at `P13J3`: the lower bound
implies `jmax(n)>=1`, replacing the global `delta*f*16>=1` guard. The new
`sr_fail13J3` theorem and its generic rank-positivity lemma kernel-check in the
`upper-bound/best` Lake environment. This closes only the SR component of the
local provider; the corresponding local-dimension R1 event bounds, their
numerical logarithm certificates, and the common-mask/port postcondition are
still open. The actual waterfill proof must also establish `n>=3832` from the
all-depth sender invariant.

The exact P13J3 interval screen confirms why simply cloning the old R1
per-event Lean wrappers is the wrong next step: its useful aggregate rates are
`lambda_a ~= 0.990128` and `lambda_b >= 9.51175`, with aggregate log sums
`-21.9116` and `-17.5193`; the old `R1aNumd`/`R1bNumd` contracts instead demand
per-event exponents `10` and `16` (and their numerical predicates fail). The
viable Lean target is the screen's closed aggregate R1 sums, including the
rational `[927/10000,928/10000]` tangent bracket for R1b, followed by the R2
sum. This keeps the proven local rank bridge useful without repeating a
known-inadequate pointwise bound.

## UB-40 maximal non-root precision gate (2026-10-24)

The coupled screen accepts `--exact-refresh-stages`; this test forced every represented active bag profile to be perfectly sorted at each non-root transition, stages 1, 2, and 3. The candidate-scale MILP solves optimally (12,580 variables, zero MIP gap; sorted-path witness passes; max inequality residual `9.6e-7`). Nonetheless it admits 2,362,826 terminal wrong keys, with 1,248,246 in one terminal block. The final threshold defect is entirely cross-bag alignment (1,248,246; local defect zero). A 133,666-wire spine mass mismatch persists while moving through bags `(1,2)`, `(2,21)`, `(3,170)`, then `(2,21)`; its magnitude does not shrink. The solution is fractional and rounded-infeasible, so this is not a network counterexample. It does show that stronger local precision alone cannot close the current selected-cut relaxation: a proof/provider must control how bag masses move across the D2 ports. Reproduce with `coupled_rank_lp.py --depth 5 --scale 8192 --threshold 1/3 --ordered-prefix --root-tail --row-stride 256 --params 3 3 2 --row-bits 13 --time-limit 120 --exact-refresh-stages 1,2,3`.

## Reduced exact-integer profile gate (2026-10-24)

A reduced gate (depth 3, scale 512, 256-row model with stride 16) solves to optimality with exact local refreshes at both non-root transitions. It has 818 variables, zero MIP gap, zero equality/inequality/integrality residual, and a rounded-valid selected-cut profile. The terminal wrong-mass objective is 31,157; the final threshold defect is 16,944 and is entirely cross-bag alignment. Thus the local-sort/mass-transfer relaxation's failure is not solely caused by fractional counts at this smaller scale. It still is not a trace of the fixed comparator network: it only certifies an integer profile satisfying the selected-cut port-transfer model. Reproduce with `coupled_rank_lp.py --depth 3 --scale 512 --threshold 1/3 --ordered-prefix --root-tail --row-stride 16 --params 3 3 2 --row-bits 8 --time-limit 120 --integer --exact-refresh-stages 1,2`.

The analogous candidate-scale integer run (`depth 5`, `scale 8192`, 13-bit rows, stride 16) reached its 120-second solver limit without an incumbent, so it supplies no integer evidence at the target scale.

## UB-40 distance-tail plus ideal-refresh gate (2026-10-24)

Combined the already certified 8192-row distance-tail caps with an ideal exact
local refresh at the first non-root transition, rather than screening either
ingredient alone. The depth-2, scale-8192 selected-cut MILP solves optimally
with 1,138 variables and 180 tail inequalities. The refresh removes all
represented within-bag defect at the final snapshot, but the terminal
cross-bag alignment remains 2,682 wires (5,094 total terminal wrong keys).
Thus the certified local tail profile and perfect local sorting still do not
control the rank-mass displacement carried through the D2 ports. This is a
relaxation diagnostic, not a concrete sorter counterexample; it says UB-40's
periodic restoration lemma must directly bound the period map on a global
alignment state, not infer alignment control from sender-local tails.
Reproduce with `coupled_rank_lp.py --depth 2 --scale 8192 --threshold 1/3
--ordered-prefix --root-tail --row-stride 64 --params 3 3 2 --row-bits 13
--time-limit 60 --distance-tail-profile
64=103/10000,128=78/10000,256=47/10000,512=25/10000,1024=12/10000,2048=61/100000
--exact-refresh-stage 1`.

## Level-weighted alignment diagnostic (2026-10-24)

The coupled LP report now includes `level_l1`: at each snapshot it sums
`|H_B-P_B|` over bags at each hierarchy level. This makes a spatial potential
testable without confusing it with the unweighted cross-bag sum. On the
existing depth-5, scale-8192, exact-refresh-at-stage-1 optimum, the level
profiles at stages 1--4 are respectively
`[0, 2627564, 0, 0]`, `[147351, 0, 2218069, 0]`,
`[0, 878806, 0, 1742856]`, and `[0, 0, 2627564, 0]` (levels 0--3).
For the exploratory weight `w_i=4^-i`, the corresponding weighted masses are
656,891; 285,980; 246,934; and 164,223. Thus this terminal-wrong-count
maximizing witness
has a contracting *weighted* profile across the four post-refresh snapshots,
even though its unweighted alignment remains about 2.63 million. The data
suggests a concrete all-depth gate: find uniform constants `rho<1` and `C`
such that the D2 one-stage transfer obeys
`V_{t+1} <= rho*V_t + C*localError_t` for
`V_t=sum_i 4^-i sum_{B at level i}|H_B-P_B|`, and prove the local-error
forcing is summable under the certified provider. This is only a hypothesis:
the LP witness is a selected-cut relaxation, the potential omits within-bag
defect, and the initial alignment is zero while the first transition creates
it. The next decisive screen must maximize the weighted potential over legal
reachable period inputs (including local defect), rather than merely report
the terminal wrong-count optimizer.

Follow-up: `coupled_rank_lp.py` now has an exact MILP drift objective
`max(V[t+1]-rho*V[t])`, with binary sign selectors for every absolute value
and an optional lower floor on `V[t]`. This avoids the invalid epigraph-only
max-absolute formulation. With weight `1/4`, `rho=1`, and `V[t]>=500`, the
depth-2/scale-8192 gate (including the certified distance tails and ideal
local refresh) is feasible and optimally gives drift `-375`: the witness has
2,000 alignment wires at level 1 and 2,000 at level 2, so the geometric
weight alone yields the factor `1/4` on that transition. But the deeper
depth-5/scale-512 gate with the same weight and `V[2]>=100` finds drift
`+9,856` from stage 2 to stage 3. Its profile changes from 30,720 wires at
level 2 to 47,104 at level 1 (with negligible other-level mass), reversing
the direction and amplifying alignment. Therefore no phase-independent
geometric level weight can contract the selected-cut transfer by itself:
the two observed directions would require its base both below 1 and above
`47,104/30,720 > 1.53`. The stage-2 witness also has within-bag defect 8,192,
so this does not rule out a coupled inequality with an explicit local-error
forcing term or a phase-dependent potential. The immediate UB-40 gate should
therefore maximize `V[t+1]-rho*V[t]-C*E[t]`, with `E[t]` the local defect and
`C` derived from the certified sender-provider bound; a positive residual at
that `C` would reject this invariant family. Both LPs are selected-cut
relaxations, not traces of a concrete fixed network.

The drift model also accepts `--alignment-local-error-weight C`, which
subtracts `C*E[t]`, where `E[t]=sum_B min(H_B,P_B)-Z_t(q)` is the represented
within-bag threshold defect. On the exact reduced depth-5/scale-512 model at
stage 2, the optimum changes from `+1,664` at `C=1` to `-75` at `C=5/4`
(both with `V[2]>=100`, level weight `1/4`, and ideal refresh at transition
1). This suggests a quantitatively plausible coupled inequality on that
reduced relaxation, but does not prove it. The corresponding scale-8192,
depth-5 run with certified distance tails, `C=5/4`, and `V[2]>=10,000`
hit the 180-second MILP limit with an incumbent drift `-3,072` and a very
large reported MIP gap; it is unresolved and cannot certify contraction.
The exact reduced command is `coupled_rank_lp.py --depth 5 --scale 512
--threshold 1/3 --ordered-prefix --root-tail --row-stride 16 --params 3 3 2
--row-bits 8 --time-limit 120 --exact-refresh-stage 1
--alignment-drift-stage 2 --alignment-weight 1/4 --alignment-drift-rho 1
--alignment-prev-floor 100 --alignment-local-error-weight 5/4`.

Period-boundary placement gate (candidate scale): moving the ideal local
refresh to the final represented transition (`exact-refresh-stage 3`) and
maximizing the weighted-state drift across that transition gives the exact
MILP optimum `+142,533.98` for `V[4]-V[3]-(5/4)E[3]`, with zero MIP gap. The
profile shifts from levels 1 and 3 at snapshot 3 (57,457 and 3,299,201 L1
mass) to level 2 at snapshot 4 (3,335,171), while represented within-bag
defect at snapshot 3 is zero. The ideal local refresh at the period boundary
therefore still does not restore the level-weighted alignment state, even
with certified tails and the `C=5/4` local-defect charge. This is a decisive
failure of the *current selected-cut refresh model*, not of every possible
precise separator: a usable UB-40 proof must model a global alignment action
of the actual precise stage. Reproduce with `coupled_rank_lp.py --depth 5
--scale 8192 --threshold 1/3 --ordered-prefix --root-tail --row-stride 256
--params 3 3 2 --row-bits 13 --time-limit 180 --distance-tail-profile
64=103/10000,128=78/10000,256=47/10000,512=25/10000,1024=12/10000,2048=61/100000
--exact-refresh-stage 3 --alignment-drift-stage 3 --alignment-weight 1/4
--alignment-drift-rho 1 --alignment-prev-floor 10000
--alignment-local-error-weight 5/4`.

## Quantified global-restoration cap (2026-10-24)

The scalar alignment-cap screen brackets the sufficient cap for this
candidate period map: at cap 50,000 the exact objective is `-3,750`; at
80,000 it is numerically zero (`1.7e-9`); at 100,000 it is `+2,500`.
Thus the selected-cut model's boundary restoration target is about 80,000
misaligned keys at the tested threshold, or `2.98e-4*N` for its
`N=8192*8^5=2^28` wires. This cap controls only the cross-bag term: at cap
80,000 the represented within-bag defect at the final cut is still about
183,112, so it cannot serve as the terminal sorting condition by itself.

For scale comparison only, the old `sub500-screen` P=8 route has conditional
cost 208.125 with cheap-stage `(x,y,z)=(4,6,3)` and `q_prec=26`; its two-round
bulk table at row height 26 corresponds to error fraction
`exp(-11.9071) ~= 6.74e-6`, about 1,810 keys on `2^28` wires. That is roughly
44 times smaller than the 80,000-key cap found above, suggesting adequate
precision headroom **if** the precise stage's proven error contract controls
the same global bag-alignment quantity. The periodic cost model and this D2
flow LP use different stage/state models, so this comparison is a research
lead, not a transferred theorem. The missing bridge is to derive a uniform
all-level bound on `q-sum_B min(H_B,P_B)` from the actual precise separator's
outsider/flow guarantees, and separately retain the within-bag error bound.

The finite-set bridge is now kernel checked in `D2RankAlignment.lean`:
`threshold_excess_le_outsiders` bounds a bag's positive threshold-mass excess
by its keys outside the target interval, and
`threshold_alignment_le_outsiders` sums this to prove
`q - sum_B min(H_B,P_B) <= sum_B outsiders(B)` whenever current bags partition
the `q` below-threshold keys. Focused check passed with
`lake env lean ../experiments/prefix-flux/D2RankAlignment.lean` from
`upper-bound/best`. This removes the combinatorial conversion gap; it does
not yet show that the actual precise stage supplies the needed outsider sum.
The next proof obligations are now specific: (i) prove the actual stage's
register bags form the required partition at each threshold, (ii) sum its
outsider caps over the live multilevel frontier and show the result is at most
80,000 (or a uniform `2.98e-4*N`), and (iii) prove that this precision stage
really reaches that outsider contract from the preceding tolerant state. The
third item is the central UB-40 restoration lemma; the accepted `P_all`
induction only preserves one fixed outsider invariant and does not by itself
establish restoration from a `T=1000` state.

## UB-40 check against the existing pathwise envelope (2026-10-24)

`D2ScheduleReserve.lean` already has the pathwise recurrence
`g' <= g/2 + rho/4` (`d2_deficit_bound_by_outsider_potential`). If one tries
to realize a 24-stage UB-40 period using only this same recurrence, with 23
cheap steps at allowance `T*R` and a final precise step at allowance `R`, then
the period map is
`g_24 <= 2^-24*g_0 + (T*R/4)*(1-2^-23) + R/4`.
At `T=1000`, its fresh-error floor is about `250.25*R`, so a precise step
that merely lowers `rho` cannot restore an `R`-scale invariant. More
quantitatively, if the refresh proves `g' <= beta*g + R/4`, then preserving
`g <= R` across the period requires
`beta <= (3/4)/(2^-23 + (T/2)*(1-2^-23))`; at `T=1000` this is about
`0.00150000018`, a reduction of at least 666.67-fold on the incoming global
state. This is an algebraic screen of the existing envelope, not a refutation
of UB-40: the precise stage would have to prove this much stronger coefficient
(or a direct reset/period-map bound). The next gate is that global restoration
action, rather than more local precision or cost re-pricing.

## UB-40: test the 80,000 alignment cap through the remaining stages (2026-10-24)

I reran the candidate-scale coupled model with the certified distance-tail
profile, an ideal local refresh at transition 1, and the previously identified
80,000 cap on cross-bag alignment immediately after that refresh. The
mixed-integer relaxation is optimal with zero reported MIP gap (11,891
variables, 28,112 inequalities; max inequality residual `9.54e-7`), but
still permits 422,144 terminal wrong keys. At the capped
snapshot, cross-bag alignment is exactly 80,000 and within-bag defect is
131,072. Two transitions later, within-bag defect is zero but alignment has
risen to 211,072, leaving terminal errors. Thus the 80,000 one-snapshot cap
is not a sufficient restoration contract even in this short selected-cut
relaxation. The profile variables are fractional and their rounding is
infeasible, so this is not a counterexample to the fixed network or the full
24-stage UB-40 period.

Reproduce with:

```text
coupled_rank_lp.py --depth 5 --scale 8192 --threshold 1/3 --ordered-prefix
--root-tail --row-stride 256 --params 3 3 2 --row-bits 13 --time-limit 120
--distance-tail-profile 64=103/10000,128=78/10000,256=47/10000,512=25/10000,1024=12/10000,2048=61/100000
--exact-refresh-stage 1 --refresh-alignment-cap 80000
```

The next gate needs a period map controlling the alignment trajectory after
refresh (or a stronger invariant that charges its later growth), not just a cap
at the refresh output.

The same gate with a **zero** alignment cap also solves optimally. It forces
alignment to zero at snapshot 2, but the receiver-local defect there is still
131,072; at snapshot 3 that defect is converted into 131,072 cross-bag
alignment, and 262,144 terminal wrong keys remain. This isolates the issue:
even an exact sender-local sort plus zero alignment at one instant does not
make the routed receiver state pure. The period state must couple alignment
with local defect across the D2 remapping. Reproduction is the command above
with `--refresh-alignment-cap 0`; the optimum has zero MIP gap and maximum
inequality residual `9.54e-7`, but again the profile is fractional and its
rounding infeasible.

The cap-zero gate was repeated with every local row cut enforced on a reduced
row scale (`row_count=128`, depth 5, scale 128). It again solves optimally:
the stage-2 alignment is zero, receiver-local defect is 2,048, and by stage 3
that defect has become 2,048 alignment; the terminal objective is 4,096
wrong keys. This model has 90,543 variables and 271,157 inequalities, with
all-row dominance, but its profiles are still fractional and rounding is
infeasible. The phenomenon therefore survives removal of row-cut sampling in
this reduced relaxation, though it remains neither a concrete network trace
nor candidate-scale evidence.

```text
coupled_rank_lp.py --depth 5 --scale 128 --threshold 1/3 --ordered-prefix
--root-tail --all-row-dominance --params 3 3 2 --row-bits 7 --time-limit 120
--exact-refresh-stage 1 --refresh-alignment-cap 0
```

An integer version at scale 32 and row height 32 also solves to optimality
(27,375 integer variables, zero MIP gap, maximum inequality residual
`7.95e-8`, and rounded profile valid). It has zero alignment and 512 local
defect immediately after refresh; one transition later the defect is 512
alignment, with zero local defect. The total threshold-cut defect remains
512 through snapshots 2--4, and 1,024 terminal wrong keys remain. This removes
fractionality as the explanation for the reduced all-row witness, while still
not providing a common input/output trace of the fixed comparator networks.
Command: `coupled_rank_lp.py --depth 5 --scale 32 --threshold 1/3
--ordered-prefix --root-tail --all-row-dominance --params 3 3 2 --row-bits 5
--time-limit 120 --integer --exact-refresh-stage 1 --refresh-alignment-cap 0`.

The integer profile screen now also reports rigorous inversion-count intervals
from its sampled global prefix counts. The interval formulas were checked on
43,691 binary-word/cut-subset cases through length 8. On this same terminal-
error-maximizing witness, the inversion count is exactly 335,675,392 at
snapshot 2, then lies in `[318,705,977, 318,741,447]` at snapshot 3 and
`[294,878,689, 295,051,327]` at snapshot 4. Thus the threshold defect can
remain 512 while inversion mass decreases across the later stages. This
supports a distance-weighted potential as a better state than the single
threshold defect, but it is one relaxed witness, not a worst-case contraction
bound. The `sampled_inversion_bounds` diagnostic is emitted by
`coupled_rank_lp.py` on integer-profile runs.

## Exact small-flow distance-moment drift gate (2026-10-24)

Added `--inversion-drift-stage/span`, `--inversion-moment-order`, and a
starting-moment floor to the coupled model. With `--all-global-cuts`, the
objective is the exact global distance moment
`M_s=sum_r lambda_s(r)*(min(q,r)-Z(r))`, not a sampled proxy. The moment
identity was checked on all 2,044 binary words of lengths 0--8 for orders
1--4. For the finite `(3,3,2)`, depth-4, scale-1 flow, the exact-cut optimum
is zero drift for `M_1` over the two-transition window with an ideal refresh
at transition 1 (starting `M_1=1,026,643`); the corresponding `M_2` gate also
has zero maximum drift (starting `M_2=3,622,957,859`). The one-step transition
1 to 2 also has zero maximum `M_1` drift, with and without ideal refresh.
These are exact optimization results for the prefix-dominance profile model,
not a proof for the fixed network or the large-depth schedule. They show that
these small phases admit equality cases, so a proof cannot assume strict
per-stage contraction from local sorting alone.

A longer exact-cut diagnostic uses `(2,2,1)`, depth 6 (seven transitions),
with three ordinary transitions followed by an ideal local refresh. Over this
four-transition period the maximum drift is again zero for both `M_1` and
`M_2`, with source moments at least 10,000 and 100,000,000 respectively.
For the `M_1` run HiGHS returned optimal status with primal/dual objective
within `8e-11` of zero (the reported relative gap is ill-conditioned at a
near-zero objective); the `M_2` run returned zero relative gap. This is a
different, lower-branching D2 schedule, so it is only evidence against a
generic strict-contraction claim, not a result for the `(3,3,2)` target.

On the same `(2,2,1)` finite flow, maximizing full-horizon
`M_1(stage 6)-M_1(stage 0)` with the refresh at transition 5 also has exact
optimum zero: both moments are 3,709,184, with zero MIP gap and primal/dual
objective within `1e-10` of zero. Thus even the complete seven-transition
profile model admits an equality path with one ideal local refresh. The
four-transition `M_3` runs with and without refresh both hit 120 seconds
without an incumbent and give no evidence either way.

Example command (two-transition `M_2` gate):

```text
coupled_rank_lp.py --depth 4 --scale 1 --threshold 1/3 --ordered-prefix
--root-tail --params 3 3 2 --row-bits 0 --time-limit 120 --all-global-cuts
--exact-refresh-stage 1 --inversion-drift-stage 0 --inversion-drift-span 2
--inversion-prev-floor 100000 --inversion-moment-order 2
```

Four-transition `(2,2,1)` diagnostic:

```text
coupled_rank_lp.py --depth 6 --scale 1 --threshold 1/3 --ordered-prefix
--root-tail --params 2 2 1 --row-bits 0 --time-limit 120 --all-global-cuts
--exact-refresh-stage 5 --inversion-drift-stage 2 --inversion-drift-span 4
--inversion-prev-floor 100000000 --inversion-moment-order 2
```

Full-horizon `M_1` diagnostic:

```text
coupled_rank_lp.py --depth 6 --scale 1 --threshold 1/3 --ordered-prefix
--root-tail --params 2 2 1 --row-bits 0 --time-limit 120 --all-global-cuts
--exact-refresh-stage 5 --inversion-drift-stage 0 --inversion-drift-span 6
--inversion-prev-floor 100000 --inversion-moment-order 1
```

### Exact integer M2 equality path (2026-10-24)

I reran the `(3,3,2)`, depth-4 two-transition gate with integer counts and
profiles, all 4,097 global prefix cuts, and the ideal local refresh at
transition 1. The MILP solves optimally (24,819 variables, zero MIP gap) and
maximizes `M_2(2)-M_2(0)` at exactly zero, subject to `M_2(0)>=1,000,000`.
The optimizer has `M_2=5,372,098,536` at all three snapshots, while the
terminal wrong-mass objective is 2,691 and 63 terminal scalar positions are
bad. Thus the equality/non-sorting witness is genuinely integral and survives
the exact global-cut representation; it is stronger than the earlier
continuous-profile equality screen. It still satisfies the selected-cut
profile relaxation rather than one fixed comparator network, so it rejects
strict M2 contraction from these constraints, not every possible reachable
state invariant.

The same exact integer model with `M_3` and source floor `10^8` also solves
optimally at zero drift: `M_3=12,260,473,842,625` at both endpoints and the
terminal wrong mass is 2,641. This makes a simple switch from inversion area
to a cubic distance penalty unpromising under the current port relaxation.

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 4 --scale 1 --threshold 1/3 --ordered-prefix --root-tail --params 3 3 2 --row-bits 0 --time-limit 120 --integer --all-global-cuts --exact-refresh-stage 1 --inversion-drift-stage 0 --inversion-drift-span 2 --inversion-prev-floor 1000000 --inversion-moment-order 2
```

For the cubic moment, change the last two options to
`--inversion-prev-floor 100000000 --inversion-moment-order 3`.

## Phase-rescaled alignment-potential gate (2026-10-24)

I tested whether a time-periodic scalar multiplier could repair the failure of the fixed `4^-level` alignment potential. On the reduced `(3,3,2)` selected-cut model (depth5, scale512, row height256, stride16), I maximized `W[t+1] - (11/10) W[t] - (11/8) E[t]` at transitions `t=1,2,3`, where `W=sum_i 4^-i * level_alignment` and `E` is represented within-bag defect. All three MILPs solve optimally with zero gap and positive maxima: `11,545.6`, `83,288.46`, and `85,501.32`. Since `11/8=(11/10)*(5/4)`, this is the same local-defect charge as the prior `C=5/4` test after rescaling the potential.

Thus a common one-step multiplier of `1.1` does not make the selected-cut inequality nonpositive on any of these three tested transitions. This is not yet a test of a complete schedule period, so it does not rule out phase-dependent scalar rescaling. It rejects only the tested common one-step scalar bound in this reduced relaxation; it does not rule out a vector of level weights, a phase-dependent state that also tracks local defect, or a stronger fixed-network reachability contract. Reproduce each optimum by setting `--alignment-drift-stage` to1,2,3 in:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 5 --scale 512 --threshold 1/3 --ordered-prefix --root-tail --row-stride 16 --params 3 3 2 --row-bits 8 --alignment-weight 1/4 --alignment-drift-rho 11/10 --alignment-prev-floor 100 --alignment-local-error-weight 11/8
```

## Arbitrary level-weight screen (2026-10-24)

`coupled_rank_lp.py` now accepts `--alignment-level-weights` to test an explicit positive weight vector instead of only `beta^level`. On the same reduced gate and transition `t=2`, with `rho=1`, source potential floor100, and local-defect charge `C=5/4`, geometric vectors `(1,beta,beta^2,beta^3)` gave optimal zero-gap drifts:

| beta | max drift |
|---:|---:|
| 1/2 | 107,892.76 |
| 1/3 | 100,908.34 |
| 1/8 | 52,744.25 |
| 1/16 | 28,750.59 |
| 1/32 | 14,982.28 |
| 1/64 | 7,860.93 |
| 1/128 | 4,043.20 |
| 1/256 | 1,981.79 |

The strong downward trend says the fixed weight `1/4` was poorly scaled for this particular transition, but no tested vector gives nonpositive drift. This is not a search over all positive vectors or phases and does not prove that no level-weighted Lyapunov function exists. It narrows the next screen: fit a normalized non-geometric vector against all transitions jointly, with enough weight retained at every terminally relevant level. The CLI option is useful for that follow-up; `python -m py_compile` passes.

### Non-geometric candidate and conserved alignment witness (2026-10-24)

On the same depth5/scale512 model, the vector `w=(1,1/2,1/2,1/2)` gives optimal drift `11,264` at transition1 and zero (within `7e-9`) at transitions2 and3. Trying phase ratios `rho=(11/10,9/10,9/10)` with local charge `C=(5/4)rho` gives optimal drifts `9,011.2`, `109,055.5`, and `109,055.5`; this vector does not admit the hoped-for compensation on the tested transitions. These are only the near-root transitions in the reduced tree, not a complete asymptotic phase cycle.

The optimizer trace for `w=(1,1/32,1/1024,1/32768)` makes the underlying issue visible: level-alignment L1 mass is `634,219.35` at snapshots2,3,4, while its distribution moves from level2, to levels1+3, and back to level2. Represented within-bag defect is zero at snapshots2--4, and the terminal wrong-mass objective is still positive. Thus this relaxation admits essentially lossless alignment circulation even when local defects have disappeared. A useful global proof must exclude that circulation using a fixed-provider/reachability property, or show that actual routing later sends it into a rank-pure terminal region. Reweighting the same selected-cut state has not supplied that missing fact.

The attempted compensation is also recorded: with `w=(1,1/2,1/2,1/2)`, phase ratios `(11/10,9/10,9/10)` and proportionally scaled local charge `(11/8,9/8,9/8)` gave positive optimal drifts `(9,011.2,109,055.5,109,055.5)` on transitions1--3. This is just a near-root diagnostic, not a complete schedule-period test. The depth8 full-period LP build and the depth5 all-row-dominance build were both stopped before producing solver results because model construction did not finish promptly; they provide no mathematical evidence.

2026-10-24 Stage 12 schedule frontier: `d2FlowCandidateStage12_frontiers` is now kernel checked for `d>=13`. It identifies level0 top-descending, levels2 and4 mid, level6 bottom-rising, and level8 inactive. This extends the actual schedule classification one transition beyond Stage11 and fixes the startup threshold for this phase. It is only the schedule frontier; no Stage12 sender gates or whole-tree invariant preservation are proved yet. The focused `lake env lean ../experiments/prefix-flux/D2ScheduleReserve.lean` run completed without Lean diagnostics.

## UB-40: precise-stage contract audit (2026-10-24)

The current accepted Chvatal API does not provide a restoration coefficient for a
precise stage. In `AKS/Chvatal/StageKernel.lean`, `StageKernel.hBadSend0`
bounds new parent-send outsiders by `parentOutMass` with coefficient exactly
one, plus sibling and local-error terms. `outsiderBound_step_of_kernel` then
uses the small invariant `hP` on the parent to recover the next small
`OutsiderBoundLe`; it has no hypothesis or conclusion for an incoming
`T`-enlarged invariant. `BadSendField.badSendField_real` has the same
unit-coefficient parent term. Therefore the existing precise-stage contract
can preserve its certified small invariant, but cannot establish UB-40's
needed reset from a `T=1000` state. This is a gap in the available theorem
interface, not a refutation of what a more global precise network might do.

The quantitative period condition from the D2 pathwise envelope is
`beta <= (3/4)/(2^(-(P-1)) + (T/2)(1-2^(-(P-1)))` for `P-1` cheap steps
`g' <= g/2 + T R/4` followed by a refresh `g' <= beta*g + R/4`, with
`g_0 <= R`. At `T=1000`, this asks for `beta <= 0.00151179` at `P=8`
(about 661-fold shrinkage) and `beta <= 0.00150000018` at `P=24`
(about 667-fold). The accepted Chvatal API's coefficient one does not meet
this condition. The next viable UB-40 step is a genuinely stronger global
refresh theorem, with a state measured against cross-bag rank alignment; more
local sorting precision does not fill this interface gap. The periodic cost
screen remains conditional, and no sub-300 construction follows yet.

## Stage 12 bottom-rise input gate (2026-10-24)

Kernel-checked `d2FlowCandidateAny_stage12_inactive_inputs` proves every
subtree rooted at level 7 or deeper has vacuous Stage-12 sender obligations.
`d2FlowCandidateStage12_botRise_inputs` reduces the level-6 gate to the single
equality `low + high = G`. `d2FlowStage_path6_tree_projection` exposes the
actual level-five parent action on each Run-12 path, and
`d2FlowCandidateStage12_actual_levelSix_balanced` proves that Stage 11's
level-five `botDesc` write supplies this equality, including saturated nodes.
The generic packaging lemma then gives
`d2FlowCandidateStage12_actual_levelSix_inputs`, the complete actual bottom-
rise input predicate for every live level-six node. The focused full-file
command `lake env lean ../experiments/prefix-flux/D2ScheduleReserve.lean`
passed with exit code 0. Stage 12's root and mid-sender input gates and
induction beyond this finite run remain open.

## Stage 12 root gate (2026-10-24)

`d2FlowCandidateStage12_root_zero` proves the actual Run-12 root deficit is
zero. It composes the established Stage-10 root reset with Stage-11's
inactive-root preservation, using the actual schedule frontier. The focused
full-file Lean check passed with exit code 0. This closes the root's local
top-descending input requirement, but Stage-12 level-2 and level-4 mid-sender
input gates and whole-tree invariant preservation remain open.

The same full-file check also verifies `d2FlowCandidateStage12_levelFour_parameters`, `d2FlowCandidateStage12_levelFour_boundary_mass_suffices`, and `d2FlowCandidateStage12_mid_inputs`. These isolate the level-four arithmetic: its capacity is `2^(3d-3)`, its quota is `15*2^(3d-15)`, and the sender-cap plus one endpoint reserve pays its quota. The actual Run-12 level-four node balance, cap, endpoint reserves, and recursive level-five input facts are not yet assembled, so this is a local gate constructor rather than an actual sender proof.

`d2FlowCandidateStage12_actual_levelFive_inputs` is now checked as well: its
inactive level-five contract follows from the actual level-six gates. This
closes the recursive-input part of the level-four mid gate. Proving the actual
level-four balance, sender cap, and two endpoint reserves remains the next
finite obligation; the level-two mid gate and the all-depth induction are
still open.

`d2FlowCandidateStage12_levelFour_endpoint_reserve` and
`d2FlowCandidateStage12_actual_levelFour_inputs` now pass the full-file Lean
check. The latter closes all live level-four mid gates in the actual Run-12
state: Stage 11's level-three mid write supplies balance and the sender cap,
its level-five bot-descending quota pays both endpoint reserves, and the actual
level-five input contract recurses to the proved level-six gates. The remaining
local Stage-12 sender band is level two; the all-depth rank-transfer invariant
is still the main global gap.

Stage-12's level-two local arithmetic and recursive packaging are kernel checked. `d2FlowCandidateStage12_actual_levelThree_inputs` packages the inactive level-three nodes from the actual level-four gates, and `d2FlowCandidateStage12_levelTwo_endpoint_reserve` proves Stage 11's level-three mid quota supplies the next level-two reserve. `d2FlowCandidateStage12_actual_levelTwo_inputs` assembles the actual Run-12 level-two gates from Stage 11's level-one top-rise update, the endpoint reserves, and the level-three input package. `d2FlowCandidateStage12_actual_inputs` then packages the full recursive input predicate, and `d2FlowCandidateStage12_preserves_inv` applies the generic theorem to prove the actual Run-12 to Run-13 invariant transition. The focused full-file check passed with exit code 0. This advances the finite schedule bridge by one stage; it does not establish the all-depth rank-transfer/refresh invariant, which remains the main global gap, so the route below 300 is unestablished.

## Coupled alignment/local-defect period gate (2026-10-24)

Extended `coupled_rank_lp.py` so the exact MILP can maximize the multi-step
drift of `V + lambda*E`, where `V` is level-weighted cross-bag alignment and
`E` is represented within-bag threshold defect. New options are
`--alignment-drift-span` and `--alignment-error-weight`; the defaults preserve
the previous one-step objective. Python compilation, CLI help, and a default
terminal-mass run passed.

On the reduced depth-6, scale-512 instance, an ideal local refresh at stage 1
followed by a three-transition window (snapshot 1 to 4) has optimal drift
`+24,576` for level weight `1/4`, `lambda=5/4`, and `rho=1` (12,178 variables,
zero MIP gap, residuals below `1e-7`). Adding 639 distance-tail inequalities
obtained by rescaling the row-height-8192 profile to 256 rows leaves this
optimum unchanged; those rescaled caps are diagnostic assumptions, not a
certified small-row tail theorem. The witness moves error from cross-bag
alignment at the start into within-bag defect at the end, so local refresh
alone does not contract this coupled potential in the selected-cut model.

For the opposite stage-2-to-3 conversion on depth 5 / scale 512, the
`lambda=1/8` MILP solves optimally with drift `+8,832`. Incumbents remain
positive through `lambda=4`, but those runs hit time limits and give no
optimality certificate. These are feasible fractional profile witnesses in
the selected-cut relaxation, not traces of the fixed comparator network.
They reject the tested fixed-weight potential as a sufficient invariant in
this model; they do not rule out a richer phase-dependent/global state. The
global rank-transfer and all-depth provider/termination gaps remain open.

Reproduce the reduced period gate with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 6 --scale 512 --threshold 1/3 --ordered-prefix --root-tail --row-stride 64 --params 3 3 2 --row-bits 8 --time-limit 120 --exact-refresh-stage 1 --alignment-drift-stage 1 --alignment-drift-span 3 --alignment-weight 1/4 --alignment-drift-rho 1 --alignment-prev-floor 100 --alignment-error-weight 5/4
```

Add `--distance-tail-profile 2=103/10000,4=78/10000,8=47/10000,16=25/10000,32=12/10000,64=61/100000` for the rescaled 256-row stress test. The exact one-step positive-drift run uses depth 5, row stride 16, stage 2, span 1, and `--alignment-error-weight 1/8`.

At the boundary weight `lambda=1/2`, the same depth-6 three-transition
refresh window solves optimally with drift `9.3e-10` (numerically zero, zero
MIP gap); its terminal threshold defect is entirely within bags. This leaves
`V + E/2` as a plausible nonexpansive candidate over this short tested window,
though not a strict contraction. Extending the window to six transitions at
depth 7 creates a 143,608-variable MILP; HiGHS reached its time limit without
a primal incumbent. Thus the period length needed for UB-40 remains untested
decisively, and the shallow nonexpansive result does not establish a uniform
period map or an all-depth invariant.

With integer counts and every row-prefix dominance cut (all 8 row positions),
the depth-6 / scale-8 three-transition drift is zero with zero MIP gap, both
with and without the ideal local refresh. The no-refresh model has 11,519
variables, zero equality/inequality residual, and a valid integral solution.
This is finite evidence for `V + E/2` as a nonexpansive D2 transfer potential
under local prefix dominance, not a sorting conclusion: the no-refresh
witness still has 9,150 terminal errors, all within bags. A phase-shifted
depth-7 / scale-8 all-row integer gate (stage 2 to 5) reached the 120-second
solver limit without a primal incumbent at 144,466 variables, so the
three-step inequality is not yet checked across the next boundary phase. The
sub-300 cost still needs a period of at least 24 stages and a precise stage
that lowers the global potential, not only local defect. This count
relaxation also does not encode one fixed comparator network or prove the
three-step inequality at arbitrary depth.

Reproduce the all-row no-refresh gate with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 6 --scale 8 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 1 --params 3 3 2 --row-bits 3 --time-limit 120 --integer --alignment-drift-stage 1 --alignment-drift-span 3 --alignment-weight 1/4 --alignment-drift-rho 1 --alignment-prev-floor 10 --alignment-error-weight 1/2
```

The potential's scalar decomposition is now kernel checked in
`D2RankAlignment.lean`. `twice_overlap_add_alignment_eq` proves
`2*sum_B min(H_B,P_B) + sum_B |H_B-P_B| = 2q` when both mass profiles total
`q`; `sum_prefix_le_sum_min` proves the local defect is nonnegative whenever
each bag's contribution to the global threshold prefix is bounded by its
actual mass and its target-prefix capacity. Consequently
`alignment_add_twice_local_defect_eq_twice_prefix_defect` gives the exact
identity `2F = A + 2E`, where `F` is the global threshold-prefix defect, `A`
is unweighted bag alignment, and `E` is within-bag defect. The focused Lean
check passes. This validates the state accounting, not the D2 transfer step;
the next proof obligation is the uniform all-depth three-stage inequality
`V' + E'/2 <= V + E/2` under the actual local prefix-dominance contract, then
a refresh theorem that reduces this potential globally.

The phase-1-to-4 depth-7 / scale-8 all-row **continuous-profile** gate was
rerun with its output captured at `LLM-helpers/sub300-depth7-span3.log`.
HiGHS hit its time limit (144,463 variables; reported MIP gap about 449%), but
returned a feasible point with objective `+792` for the maximization of
`V_4 + E_4/2 - V_1 - E_1/2`; primal equality/inequality/bound residuals were
at most `4.4e-8`, and its piecewise sign selectors were integral. This is a
valid positive-drift witness in this profile relaxation, not an optimum and
not a trace of the fixed comparator network. It shows that the proposed
uniform three-stage inequality does not follow from the current continuous
all-row local-prefix constraints alone. The depth-6 zero-drift optimum is
therefore depth-specific evidence only. Any revival of this route needs a
stronger transition contract (e.g. fixed-network correlations or additional
cross-cut constraints), or a different potential; do not extend the present
Lean bridge as if `V + E/2` were already a valid global invariant.

## Fourth-moment equality gate (2026-10-25)

The depth-4/scale-1 all-global-cut gate with an ideal refresh at transition1,
using `M_4`, solves optimally at zero drift with source floor `10^6`. The
returned solution is integral despite a continuous profile model:
`M_4=1,000,541,859,856,575` at all three snapshots, with1,447 terminal wrong
keys and maximum64 in one terminal block. The solver reports zero residuals.
This is another equality witness for the selected-cut relaxation, not a trace
of the fixed network. It makes distance powers through degree4 poor standalone
global potentials; it does not show a common witness preserving all moments.
The exact command and scope limits are recorded in
[`HIGHER-DISTANCE-MOMENT.md`](HIGHER-DISTANCE-MOMENT.md).

The stronger all-row local-prefix version also has a fractional feasible
witness with the complete global prefix-defect profile unchanged pointwise
across both transitions (3,414 nonzero cuts; maximum 673). This rules out
further unweighted moments of that marginal profile as a contraction
certificate in this relaxation. It does not rule out a fixed network; the
next candidate state must encode transfer correlations across cuts/ports.

The one-step depth-3/scale-1 integer gate confirms zero fourth-moment drift
with all 513 global cuts and all-row local prefix dominance; its exact integer
profile transfers defect from within-bag to cross-bag while preserving every
global cut. This is still a relaxation rather than a fixed-network trace. The
larger depth-4 integer gate timed out after 90 seconds without an incumbent,
so it is inconclusive. Details and the reproducible smaller command are in
[`HIGHER-DISTANCE-MOMENT.md`](HIGHER-DISTANCE-MOMENT.md).

2026-10-25 probability-screen update: a rational R1b tangent bracket closes the selected F2 envelope at `f=9`, `n=8307`, support cap 18, with `ln(2P1)<=-7.50129` and `ln(2P2)<=-7.67752`. This improves the earlier unbracketed `f=11` closed screen. It still does not cover the observed `fÃ¢â€°Ë†2.45` sender, and the generic `hf16` Lean guard remains incompatible with `delta*f*n=18`; see `D2-SPARSE-BOTTOM-300.md` and `ragged_provider_probability_screen.py`.

2026-10-25 sampled B2 recurrence update: at actual row height8192, the depth-2
integer cut relaxation with stride128 solves to 1,310 terminal wrong keys
(zero MIP gap). Its terminal threshold defect is997: cross-bag alignment655
and within-bag defect342. This is an integral selected-cut flow, not a fixed
comparator trace; only sampled B2 cuts are imposed. The exact full-cut MILP
timed out without a primal solution. See `D2-DISTANCE-TAIL-PERIOD-GATE.md` for
commands, residuals, and scope.

2026-10-25 structural lead: `D2-PORT-VARIANCE-TRANSFER.md` derives an exact
all-port discrepancy bound from the weighted variance of the sender's
column profile. A uniform fixed-core cap `A_w<=48*n` at row height8192 implies
less than `1/1672` sender-mass error for aligned rectangular prefix and
common-row-band ports; the rectangular arbitrary-per-column-slice bound
remains `1/836`, and ragged masks still need a separate normalization proof.
The existing two-round random-core expectation recurrence gives about14.17
full-variance units per column from a worst-case 64-column profile, so this
cap is a plausible screen target, not a theorem: the uniform fixed-scramble
tail/provider and its transfer through the D2 flow remain open.

2026-10-25 fixed-core variance attack: a vectorized direct evaluator for a
seeded `8192 x 64` two-round core was checked against 100 literal small cases.
The constant-time incremental evaluator was cross-checked against full
recomputation over 5,000 random moves. Across 256 annealed searches of 50,000
proposals, the largest total column variance found was `A_w=1498.43` (`23.41`
per column), below the proposed cap `48*64`. This is a heuristic lower witness
for one random core, not a uniform upper bound or a proof that the core meets
the construction's provider conditions.
See `D2-PORT-VARIANCE-TRANSFER.md` and
`d2_variance_fixed_core_attack.py`.

The earlier general Cauchy allowance `1/836` reduced terminal wrong mass in
the selected-cut MILP from 1,310 to 1,254, with zero MIP gap, but left
threshold defect 969 (alignment 627, within-bag342). The sharper rectangular
prefix allowance is `1/1672`; see the next gate result. Both remain screens,
not a global recurrence proof.

The sharper prefix-specific allowance `1/1672` leaves a zero-wrong-mass
incumbent after a 300-second selected-cut MILP, but the dual bound still allows
626 wrong keys (MIP gap 0.00364), so the purity result is unproved. The
all-row aggregate-area alternative at `53/8192` built 413,230 variables and
timed out without a primal solution. Both findings are recorded in
`D2-PORT-VARIANCE-TRANSFER.md`.

The prefix-specific cap and aggregate-area formulas now have exact small
profile checks: 1,270 rectangular profiles for the sharper prefix and area
inequalities, in addition to the 278,912 ragged-band transfer cases. A full
row-stride-1 LP with the `1/1672` cap also timed out without a primal solution
at 409,846 variables; the sampled model is the tractable diagnostic.

The coupled LP now optionally enforces concavity of sampled row-prefix
profiles, a necessary consequence of the final column sort. At stride128,
this tightens the 1/1672 MILP dual allowance from 626 to 579 terminal wrong
keys, still with only a zero-wrong incumbent. At stride64, the continuous LP
has an optimal fractional witness with 587.28 wrong keys, so the cap and
sampled profile shape still do not prove purity. HiGHS incorrectly reports
the matching stride64 MILP infeasible despite a checked feasible sorted
witness; do not use that MILP status as evidence. See the variance-transfer
note for exact commands, residuals, and limits.

The stronger sparse prefix-area cone constraint, using the valid rectangular
`Gamma=48` defect-area bound and disjoint Lipschitz cones, reduces the optimal
continuous terminal wrong-mass relaxation from 388.69 at row stride128 to
37.44 at stride1. The decreasing sequence (strides 128,64,32,16,8,4,2,1)
shows sampling resolution mattered, but the full-row optimum remains positive.
It has 409,846 variables, 131,485 equalities, 1,302,552 inequalities, and
primal residual `6.4e-10`; it is an optimal relaxation value, not a sorting
counterexample. This closes the sparse-area diagnostic: more cut sampling is
not enough. Next screen a costed exact terminal cleanup or strengthen the
transition/profile constraints. The fixed-core `Gamma=48` provider and the
global all-depth rank recurrence are still unproved.

At `Gamma=32`, the stride4 continuous relaxation is optimal with 53.36 wrong
mass, compared with 68.19 at `Gamma=48`; this tighter provider target helps
but does not close the gate. The full-row `Gamma=32` model reached its 180s
HiGHS limit without a primal solution (409,846 variables, 1,302,552
inequalities), so it gives no bound. The detailed derivation and run data are
in `D2-PORT-VARIANCE-TRANSFER.md`. This reinforces that the missing step is a
stronger local-transition/rank interface; the continuous relaxation can still
retain a large inversion proxy despite the prefix-area constraints.

The aggregate port-l1 transfer is now an explicit LP constraint. In the
optimal `Gamma=48`, stride4 relaxation it lowers wrong mass from 68.19 to
60.66; dropping the pointwise `1/1672` cap changes this by less than `3e-11`.
Port-l1 alone gives 705.45 wrong mass, versus 8,501.74 with neither l1 nor
area constraints. Thus area shape is the main local tightening and aggregate
port coupling adds useful strength, but their combination still permits
cross-bag alignment. The next interface is to use the D2 endpoint reserves to
absorb this aggregate leakage; a mere l1 rank-error recurrence is noncontractive.
Exact small ragged partition checks now cover 2,654 cases. See
`D2-PORT-VARIANCE-TRANSFER.md`.

There is a promising numerical fit to the existing D2 reserve invariant:
assuming the `Gamma=48` fixed-core provider, exact reference-port/rank map,
and all-depth `a/c<=279/256`, aggregate l1 port error is `<c/512`, with
one-sided leakage `<c/1024`. These sit below the scheduled deficit/quota/end
reserve scales `c/512`, `c/256`, and `c/128`. The rank-error-to-`G,L,H`
absorption lemma is not proved, so this is a target interface, not a closed
induction. The port l1 recurrence alone is only nonexpansive; reserve
absorption is essential to avoid accumulating an `O(N/m)` loss each stage.

The one-step rank-error arithmetic now closes conditionally: parent error
`<=c/512` plus aggregate local l1 error `<c/512` gives each child error
`<c/256`; the D2 schedule doubles child capacity at the next active stage,
so this is the same normalized `1/512` invariant. This is a plausible way to
use the saturated-aware flow state instead of seeking contraction of the
selected-cut LP's looser alignment potential. The actual `G,L,H` interpretation,
all-depth schedule cases, ragged port identity, and terminal off-spine purity
are still open. The derivation is in `D2-PORT-VARIANCE-TRANSFER.md`.

The `(3,2,2)` 4096-row candidate's three-cyclic-round core now has an exact
row-height reduction: its centered output depends only on the 64 input
residues modulo64 and the sum of their quotients modulo64, all representable
at row height512. The `(1,35,17)` heuristic search finds output range8 at both
row heights. An exact 64-column SMT query for range at least20 times out at
120 seconds under the correct all-zero-offset schedule. Thus the finite
reduction is derived exactly on paper (not yet Lean-formalized), but the
needed uniform `Gamma=48` provider is still not certified. Details and the
extended SMT script are in
`D2-PORT-VARIANCE-TRANSFER.md` and `d2_cyclic_range_smt.py`.

The sparse three-round MILP is now available as a second exact encoding. It
matches direct simulation at width8, but the width64 range-20 query also times
out at120s. Solving its LP relaxation for all63 output separations gives the
last-round upper bound `(15*delta mod64)`, pruning19 separations but leaving44
unresolved. This is a diagnostic reduction only; no full provider bound is
claimed. See `D2-PORT-VARIANCE-TRANSFER.md` and `d2_cyclic_range_milp.py`.
A fixed-width QF_BV encoding with independently checked 8-column witnesses
also times out at the 64-column `delta=2` gate after60s; see
`d2_cyclic_range_bv.py`.

A structured zero-offset slope sweep found `(1,5,25)` (successive powers of5)
with heuristic range7 after24Ãƒâ€”15,000 moves, versus range8 for `(1,35,17)`.
Its per-round dilation conjugacy is recorded in the variance-transfer note,
but the shared quotient residue remains coupled across stages. The 64-column
fixed-pair range-20 MILP for `(1,5,25)`, `delta=1`, also timed out at60s.
This is a new design lead, not a provider bound.

The first four powers `(1,5,25,61)` tested as the four shuffle rounds of the
2048-row/five-sort candidate have heuristic range5 and `Aw/64=0.76514` after
64Ãƒâ€”50,000 moves on the complete residue domain. The generalized QF_BV model
passes a width8 four-round direct check but times out on the width64
range-20/separation-1 gate after60s. This suggests the 292.5 cost candidate's
local provider may be easier than the 4096-row route's, but does not prove it;
the 292.5 network's packed final-row replacement still needs separate dense
profile accounting. See `D2-PORT-VARIANCE-TRANSFER.md` and
`d2_cyclic_range_bv.py`.

The 2048-row five-sort variant was also screened with its actual support-28 packed final layer (`d2_packed_final_core_screen.py`), rather than the earlier all-cyclic approximation. Incremental updates matched full recomputation on 500 accepted random moves at 64 rows and 100 at 2048 rows. At 2048 rows, 64 starts x 50,000 moves found dense area `Aw=49.96875` (`Aw/64=0.78076`, output range6); the smaller 24 x 20,000 run found `Aw/64=0.68738`, range5. This keeps the local provider plausible in heuristic search, but is not a uniform area/rank-profile bound. The conditional cost remains292.5; the rank-transfer and terminal-purity proof are still missing.

An exact case split sharpens the packed-layer screen. Each cyclic round has
output heights `Q+R_c` with `0<=R_c<=64`, so its height range is at most64.
For the support-28 last layer, if its input heights are all in `[28,2020]`,
the first28 rows are full and the last28 empty; the packed final layer then
agrees exactly with the all-cyclic slope61 layer. If this condition fails,
either all heights are at most91 or all are at least1957. The exceptional
inputs have at most5824 minority wires in the whole 2048x64 bag. This isolates
the effect of the packed repair to low/high absolute-mass fringes; a uniform
output-area bound for these fringes is still missing.

The exact dense-interior range gate is implemented in `d2_cyclic_range_bv.py`.
For slopes `(1,5,25,61)`, the QF_BV query for any output pair with separation
at least12 (normalized by translation symmetry to compare output column0 to
the minimum) timed out at120s. This threshold is exactly useful: range at most
11 would imply `Aw <= 64*11^2/8 = 968`, below the `0.0085*2048*64` area
budget1114.112. The translation-normalized gate was sanity-checked against
width8 direct witnesses. The 64-column timeout gives no verdict; the dense
uniform bound remains open.

I also added an endpoint-count encoding for the exact cyclic residue gate:
interval coverage obeys `F_x=F_(x-1)+1-E_x`, where `E_x` is the count of
intervals ending at x, after reindexing by the slope. It matched direct
coverage on 3,000 random profiles and passes the width8 all-separations check.
The 64-column `(1,5,25,61)` query for range at least12 still times out at120s;
this is a compact recurrence for analysis, not a provider certificate.

The 4096-row alternative has a parallel exact packed-layer split. With 40
repaired edge rows, the packed last layer agrees exactly with the all-cyclic
last round whenever all incoming column heights lie in `[40,4056]`. The
preceding cyclic rounds give height range at most64; if this interior condition
fails, all heights are at most103 or all are at least3993, so the input has at
most6592 minority wires. The natural three-round slope candidate `(1,5,41)`
was screened with the endpoint QF_BV encoding at the useful threshold17
(range at most16 would imply `Aw<=2048`, below the local budget2228.224 and
consistent with `Gamma=32`). The any-separation query timed out at120s. This
leaves the 4096-row route's dense provider open as well; it is a lower-cost
alternative, not a proved improvement.

The standalone D2 reserve module was checked directly with
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` from `experiments/runaware`;
it completed without diagnostics (about11 minutes on this checkout). This is
kernel checking of the schedule/tree reserve scratch through Stage12, not an
all-stage invariant or sorting proof. A follow-up quantifier audit corrected
the earlier proposed size-weighted union over sender occurrences in
`MODERATE-TAIL.md`: its local tail event is already universal over every
input profile for one geometry. If separate deterministic cores may be chosen
per geometry, only the local clauses (bulk, fringe, directions, baselines)
need a probability union for that geometry; no factor for the number of
scheduled senders or stages is needed. The finite small-sender audit therefore
refutes only the alternative of exact-sorting them in a short terminal window.
The fixed-eta local spill bound at minimum dimensions and the global
rank-transfer induction remain open.

2026-10-26 UB-34 reuse gate: the corrected `N_CERT=64`, row-height8192
margin-tail profile lowers the depth-2 integral selected-cut optimum from
8,980 to6,390 terminal wrong keys (28.8%), but leaves63 impure blocks.
Adding sampled final-column profile concavity lowers the matched fractional
optimum only to6,022; the integral solve times out without a primal point.
An optimistic aggregate port-l1 contract at `Gamma=48` lowers the fractional
optimum further to741, but still does not force purity. Even `Gamma=0` plus
the exact integer mass-residue reference correction leaves31 keys at depth2
and254.22 at depth3, at a roughly stable `6e-5` fraction. These gates point
to global alignment transfer or a priced cleanup, not further scalar local
tail tightening. They are selected-cut relaxations, not network traces. Full
commands and scope are in [`D2-DISTANCE-TAIL-PERIOD-GATE.md`](D2-DISTANCE-TAIL-PERIOD-GATE.md)
and [`D2-PORT-VARIANCE-TRANSFER.md`](D2-PORT-VARIANCE-TRANSFER.md).

The conditional variance bridge is now kernel checked in
`D2RankAlignment.lean`: `half_variance_le_range_sq_div_eight` proves the
finite Popoviciu estimate, and `nat_half_variance_64_le_225_over_eight`
derives `A_w/64 <= 225/8` from conserved total mass and a width-64 range-15
premise. The same file proves `cyclic_successor_indicator_count_le`, the
one-sided hit-count inequality for cyclic successor thresholds with a unique
wrap, then instantiates it as
`slope35_adjacent_height_difference_le_one` for every adjacent destination
pair in the slope-35 modulo-64 shuffle. The focused
`lake env lean ../prefix-flux/D2RankAlignment.lean` check passes from
`upper-bound/experiments/runaware`. The residual-profile step is now checked;
the same file now also proves `residueHits64_eq`, the concrete source-row
residue equivalence, and the quotient/residue output formula for the physical
slope-35 shuffle on arbitrary natural heights. Thus the one-sided gradient
invariant is checked through the full local shuffle. The final slope-17
max-plus range certificate and global all-depth rank-transfer proof remain
open.

### Stage 13 level-three recursive gate (2026-10-26)

`d2FlowCandidateStage13_actual_levelThree_inputs` now assembles the actual
level-three mid-sender inputs from the Stage-12 level-two cut, the Stage-13
endpoint-reserve transfer, and the already checked actual level-four and
level-five gates. The focused full-file command
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` completed with exit code
0 and no diagnostics. This closes Stage 13's level-three recursive input
case only; its level-one input case, complete Stage-13 input predicate, and
preservation transition remain open. It does not address the global provider,
rank-transfer, or terminal-sorting obligations.

### Stage 13 actual transition (2026-10-26)

The Stage-13 top-rise gate is now derived with its exact scale: capacity
`2^(3d-14)`, quota `2^(3d-22)`, and the predecessor Stage-12 level-two
mid quota `15 * 2^(3d-21)`. The inactive level-one projection connects the
actual Run-13 level-two nodes to those Stage-12 updates. Using this, the
actual level-one gate, the previously checked level-three/level-five gates,
and the inactive root yields `d2FlowCandidateStage13_actual_inputs`.
`d2FlowCandidateStage13_preserves_inv` proves the actual Run-13 to Run-14
transition. The full focused check
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` completed with exit code
0. This is one more finite stage, not the all-stage schedule induction or the
global local-provider/rank-transfer/terminal-sorting proof.

### 4096-row dense-area gate correction (2026-10-26)

The earlier comparison used `1114.112`, which belongs to the 2048-row
alternative. For the 4096-row core, the dense-interior allowance is
`Aw<=2048` (full local target `2228.224`). The exact-integer scan over all
1024 odd slope pairs modulo64 finds the best independent pairwise-area bound
`Aw<=4659/4=1164.75`, attained for `(previous,final)=(1,49)` among others.
Thus this bound clears the 4096-row dense-interior area gate, conditional on
the one-sided-gradient lemma and the exact DP table. It does not handle the
packed core's low/high sparse fringe cases, nor prove all-cut rank transfer or
terminal sorting. The DP still needs a kernel-checked certificate and wiring
to the packed final layer. Details are in
`D2-FOUR-SORT-4096-CANDIDATE.md`; the reproducible integer evaluator is
`d2_slope_pair_screen.cpp`.

### Slope-49 local two-shuffle provider (2026-10-26)

The 64 slope-49 dual tables now export and kernel-check the original adjacent
height-transition inequality, not just their compressed suffix/local checks.
`D2Slope49Provider.lean` imports all 64 modules and proves that every profile
with the slope-35 one-sided gradient has final output range at most 13. The
same module applies the existing Popoviciu lemma to obtain
`A_w/64 <= 169/8 = 21.125`.

`D2Slope49Physical.lean` proves the exact quotient/residue formula for the
physical slope-49 row permutation following slope 35, and that each 64-row
intermediate band has output height at most 64. The provider then composes this
with `slope35PhysicalOutputHeight_gradient` to prove
`slope35_then_slope49_area_per_column_le_169_over_eight` for the actual pair
of cyclic shuffles, for every 64-column input profile with source heights at
most 64. For the unmodified cyclic final layer this gives `A_w <= 1352`, below the 4096-row dense-core allowance
2048. The focused Lean checks passed for `D2Slope49Physical.lean` and
`D2Slope49Provider.lean`; all 64 certificate modules compiled with the
table-to-edge bridge enabled.

The packed final repair changes the edge-row permutations, so this result does
not yet establish the dense gate for that modified network. An audit found the
packed screen had put bottom-row ones at the zero-packing offset; the reflected
map actually puts them in the complementary interval. After correcting the
full and incremental simulators, 64 starts x 50,000 steps on the `(1,35)` plus
packed-49, 40-edge-row schedule found `Aw=104.21875` (range 8), still only
heuristic evidence. Incremental updates matched full recomputation across 300
random mutations at each of three geometries. The packed dense/sparse provider,
all-depth rank-transfer invariant and terminal exact sorting remain open, so
the 277.5 candidate is still not a sorting-network upper-bound theorem.

Audit correction (2026-10-26): `d2_packed_width_dp.cpp` does not model the
fixed packed core's arbitrary middle-row active sets. It represents every
row, including unsorted middle rows, by a cyclic interval determined only by
its width. Therefore its reported exact range28, area bound6240.5, and
reverse/rotate screens apply only to that restricted toy model; they are not
valid bounds for the fixed core. The actual `d2_packed_final_core_screen.py`
preserves arbitrary middle-row subsets, but its results are heuristic. The
uniform packed local provider remains open and should be derived from the
actual fixed transition.

The corrected `d2_packed_reachable_range_milp.py` gate keeps arbitrary column
subsets in middle rows and only packs edge prefixes. On the low-fringe
one-sided-gradient superset `h<=103`, its LP relaxation gives pair `(40,12)`
upper bound45.91; the integer solve timed out at120s with incumbent7 and dual
bound41, hence no useful certificate. A longer actual-core hill climb of64
starts x100,000 steps at `(1,35)` plus packed49 again found `Aw=104.21875`
(range8), still heuristic. The packed local provider and global rank transfer
remain open.

The direct low-fringe gradient-class screen is more adverse: `d2_packed_gradient_adversary.py`
uses arbitrary middle-row active sets and found `Aw=1429.9921875` (range25)
after64 starts x100,000 moves; a second run with128 starts x200,000 found
`Aw=1332.2421875`. Both are below the 2048 dense allowance but are not
uniform bounds. Its incremental updates matched full recomputation over2,000
accepted mutations. The exact area MILP over this enlarged class timed out at
120s with no primal solution; the pair-range MILP remains inconclusive as
recorded in the candidate note.

The `Aw=1429.99` gradient-class witness itself has no preimage under slope1
followed by slope35: `d2_slope35_preimage_gate.py` returns solver-certified
infeasible for the exact unary integer model (4,096 binaries,4,160
constraints). This is finite solver evidence, not a Lean theorem. The more
faithful low-fringe reachable-core range model in
`d2_packed_reachable_core_range_milp.py` directly composes both shuffles and
the edge repair; HiGHS found no incumbent for either global range or fixed
pair `(40,12)` within120s. Its LP relaxation still allows a pair difference
of45.91. So the reachable-state restriction is real, but current MILP
formulations do not yet turn it into a proof.


## Slope-25 fixed-core provider (2026-10-26)

In the 4096-row local core, replacing the final slope49 by slope25 after slope35
preserves the four-sort conditional coefficient260 and yields a kernel-checked
dense provider. `D2Slope25Abstract.lean`, all64 generated certificate modules,
`D2Slope25Physical.lean`, and `D2Slope25Provider.lean` compile. The certificate
family proves output pairwise height range at most13 for every one-sided
slope-35 input profile; Popoviciu gives total centered area at most1352, below
the core's dense allowance2048. Python's integer verifier independently checks
all64 potential tables, whose largest budget sum is77.

The unmodified slope25 final layer also passes `first_failure(40,64,25,4096,2)`:
all215,308 sorted top/bottom profiles of mass at most40 have maximum output
load2. This is an exhaustive finite Python gate, not yet a Lean theorem. Thus
the unmodified local core now has both a dense bound and a sparse edge screen.
The global all-depth alignment/rank-transfer induction and exact terminal
cleanup remain open, so coefficient260 is still only a conditional stage price.
The pairwise-square DP suggests the stronger area value1230.25, but this has
not been formalized and is not part of the checked provider.


### Update: full-height phase lift and area transfer checked (2026-10-26)

The previous correction above is superseded by the kernel-checked lift modules
`D2Slope25Lift.lean`, `D2Slope25LiftRange.lean`,
`D2Slope25LiftProvider.lean`, and `D2Slope25LiftArea.lean`. The scalar
residue-hit split proves the slope35 quotient/residue decomposition for
arbitrary natural input heights. The slope25 uniform-offset identity then
rotates the destination by `25*Q` while adding the common quotient `Q`.
Composing with the residual provider gives output range at most13 and centered
quadratic area per column at most `169/8`, equivalently total centered area at
most1352, for every 64-column natural input-height profile. The area proof
transfers the residual certificate through a common offset and a permutation
of destinations.

This closes the local dense-provider gap for the 4096-row D2 core. It does not
close the global all-depth rank/alignment transfer, the exact terminal cleanup,
or the construction bridge to a complete sorting network. The support-40 sparse
edge enumeration remains a separate finite Python gate, not yet a Lean theorem.


The local core-to-port bridge is also checked in `D2Slope25LiftArea.lean`.
For input column heights at most4096, the two-shuffle output respects the
4096-wire column capacity. The full-height area theorem then gives aggregate
local `l1` deviation at most416 from uniform-density port counts for every
complete interval partition across the 64 columns. This is not yet the exact
rank-prefix transfer on ragged fixed masks and does not establish global
contraction.

### Row-major rank-prefix correction identity (2026-10-26)

`D2RowMajorMismatch.lean` kernel-checks the exact discrepancy between the
64-column uniform-density reference and the true flattened rank prefix. The
discrepancy vanishes outside the boundary row containing the cut and equals
`min(r,s) - s*r/64` within that row; it is always between0 and16. The module
also kernel-checks the exact discrete total variation of that single bump and
proves it is at most32. It also kernel-checks the transfer from this variation
to total exact-rank mismatch over every complete flattened port partition.
The theorem `rowMajorUniformPrefix_eq_flat_column_sum` proves the cumulative
identity equating a flattened boundary's sum of column-uniform prefix masses
with `rowMajorUniformPrefix`. `D2Slope25RowMajorBridge.lean` composes these
results with the local 416 fixed-core port-deviation theorem to obtain a
kernel-checked 448 aggregate exact-rank allowance for each complete
4096-by-64 sender partition, or `7/4096` of sender capacity. Connecting that
allowance to an all-depth alignment contraction and proving terminal cleanup
remain open. The new integer wrapper also uses mass conservation and
`balanced_port_directional_leakage` to bound each direction by224 wires.
After multiplying by the D2 flow scale8192, that allowance fits the existing
`capacity/512` sender-deficit budget for one `2^18`-wire tile. This is only a
numerical fit: identifying the local leakage with the reachable flow's `G`
deficit, transferring it across a multi-tile sender and maintaining the bound
through every stage remain unproved.

### Terminal schedule exact-cap check (2026-10-26)

`D2TerminalSchedule.lean` now kernel-checks the exact final active stage of
`tfD2(d)=3d-14`: the activity inequalities and parity permit only level
`d-4`, whose native capacity is exactly4096 wires for every `d>=7`. Thus, if
the proposed `1/512` physical rank-error invariant reaches this frontier, its
error is at most8 keys per threshold. This fixes the terminal scale, but it
does not prove the invariant or sort/repair the remaining outsiders; terminal
cleanup and the all-depth rank transfer remain open. The parent
`D2ScheduleReserve.lean` and this endpoint module were kernel-checked with
`lake env lean` in the run-aware package.

### Convexified fixed-core transfer gates (2026-10-26)

`coupled_rank_lp.py --continuous-slope-core` now adds the deterministic local
two-shuffle map while relaxing each sorted Boolean occupancy to `[0,1]`. This
is an outer LP relaxation of the fixed core, not a network trace. At depth2,
scale64, row height2, and target parameters `(3,3,2)`, its optimal
`max_total_wrong` is `532.75`, versus `554` for the matched profile-only LP
(13,401 versus 5,209 variables). The final maximum global-prefix defect is
`290.2734375`, versus `298.5` in the matched baseline. The fixed-core
constraints therefore remove some locally feasible profiles in this shallow
gate.

At depth3, the same terminal objective is `2,218` with and without the
continuous core. The core model solves optimally at 53,337 variables and 64
tiles; its maximum global-prefix defect is `1,194.5` at all three snapshots,
while the baseline goes `1,365 -> 1,365 -> 1,194.5`. Thus this objective gives
no further gain at the next depth. The direct inversion-area transfer gate is
also a warning: at depth2 with `M_1 >= 100,000`, the maximum of
`M_1(out)-0.99*M_1(in)` is positive for both baseline (`+1,671.32`,
`M_1=167,132` at both ends) and core relaxation (`+1,618.01125`,
`M_1=161,801.125` at both ends). It rules out a `0.99` contraction claim for
this state in these relaxations.

The core-constrained depth3 inversion-drift LP did not return a primal point
within 120 seconds (53,337 variables); this is inconclusive. The Boolean
row-height-one target gate also has no incumbent. The Boolean row-height-two
toy MILP has a feasible objective incumbent74 and dual-bound upper value84,
against baseline84.5, but its MIP gap is1.0. These finite screens indicate
that exact/convexified local core geometry can sharpen a shallow terminal
bound, but global rank transfer still needs a spatially coupled state beyond
the total inversion-area moment. No coefficient improvement is proved.

The optimizer for the core-constrained depth2 `M_1` gate has a stronger
diagnostic: its entire global prefix-defect vector is stationary from stage0
to stage2 (maximum coordinate change `3.5e-13`), while 503 of 1,025 entries
are fractional. The profile is in the ignored
`LLM-helpers/sub300-core-inversion-profile.json`. This is a fixed point of the
convexified local-state relaxation, not a Boolean input trace; it shows that
global prefix moments alone cannot certify contraction in this state space.

To reduce the exact height-two MILP, the source now represents each shuffled
two-bit column by its OR and AND instead of two unary output binaries. The
identity matched the full physical map on 1,000 random profiles. However, the
reduced `(1,1,1)` toy model still had no primal/dual point after 120 seconds
(2,343 variables, 1,024 binary variables, four tiles), so the Boolean core
gate remains unresolved.

2026-10-27 column-refined rebatching bridge: `D2Slope25LiftArea.lean` now
kernel-checks a 416 l1 bound before summing error across output columns,
`D2RankRebatch.lean` proves rational l1 error cannot increase under any
finite regrouping, and `D2ColumnRebatchBridge.lean` composes them for arbitrary
groups such as `(next tile,column)`. This removes the arithmetic obstacle to
splitting ports at per-column/partial-tile offsets. Focused Lean compilation
of all three modules passed with outputs directed to ignored `LLM-helpers`.
The proof still assumes a complete cut partition within each output column
and an explicit group map; constructing those from the scheduled D2 wire
addresses and identifying the regrouped counts with the next-stage physical
profile are the next semantic bridge. No all-depth invariant, terminal proof,
or sub-300 sorting theorem follows yet.

2026-10-27 D2 semantic stage adapter: `D2LiftedShuffleBridge.lean` now
kernel-checks that one actual `semanticExec` sort-scramble-sort stage maps any
4096-by-64 column-prefix Boolean input to its row-shift height profile, and
that the stride-35 then stride-25 `semanticExec2` network maps it to the
`fullHeightTwoShuffle` profile. This closes the local network-semantics
adapter for the dense two-shuffle core. Every column-monotone input is now
shown to have the required prefix representation, and the two-shuffle macro
preserves column monotonicity. The actual scheduler's ragged tiles and ports
are not yet connected to this fixed 4096-by-64 state, and there is no global
rank-invariant or sorting theorem.

The same bridge now also composes the kernel-checked 52-row variance bound
with the Boolean output profile: `semanticExec2_two_stride_flat_cut_band`
localizes false and true outputs to within 3392 wires of the global Boolean
cut. Threshold-map commutation, exact profile-mass conservation, and the
input/output cut-count identity now lift this to
`semanticExec2_two_stride_rank_interval`: each output key is within a 3392
wire rank interval of its rank among the keys in that fixed tile. The
all-stage D2 schedule still has to realize fixed 4096-by-64 tiles with sorted
columns and carry this local rank information across ragged ports; global
rank invariance and the sorting theorem remain open.

The scheduler-to-tile address audit is sharper now. Using `(3,3,2)`, consistent
with the candidate's `15/4096` quota, the depth100 exact screen checked 556,565
reachable tree states and 1,634,784 ordinary child cuts:
node deficits/allocations/child blocks are 4096-aligned, endpoints and
half-ports are 2048-aligned, ordinary quotas are 8192-aligned, and both
ordinary cut fronts and each child cut are 4096-aligned. `D2CutAlignment.lean`
kernel-checks that 4096-grid fronts and child boundaries give 4096-grid cuts.
It now also proves `d2FlowCandidateQuota_dvd_8192` for every active ordinary
sender at every depth `d Ã¢â€°Â¥ 7`, using role-sensitive frontier bounds. Thus the
conditional run theorem `d2FlowCandidateRun_tileAligned_of_frontContracts`
needs only the recursive front-alignment contract; quota divisibility is
discharged formally. The actual scale-8192 initial tree is proved aligned.
The all-depth front contract is now proved by induction from the stage-zero
reset and the coupled root/descendant endpoint invariant. This proves the
candidate run's 4096 tile alignment at every stage; it does not imply that
every endpoint field is 4096-aligned or establish global key-rank transfer.

2026-10-27 D2 child-front induction step: `D2CutAlignment.lean` now
kernel-checks `d2FlowStage_ordinary_child_rootAligned`: an ordinary sender
with 4096-aligned endpoints, an 8192-divisible quota, and tile-aligned child
blocks writes 4096-aligned deficits and endpoints to each child. The
`topDesc` parent case clears child root data and has a separate checked lemma.
The actual schedule theorem `d2FlowCandidate_activeOrdinary_parent_cases`
shows that an active ordinary child (from stage 3 onward) has an active
previous-stage parent, and that parent is either `topDesc` or ordinary;
`botRise` is excluded. The combined theorem
`d2FlowCandidate_activeOrdinary_child_rootAligned_next` applies this schedule
classification and the candidate quota to the two local child-update cases.
The new recursive predicate `d2FlowStageOrdinaryEndpointsAligned` is a cleaner
induction target than raw front divisibility: combined with tile alignment it
implies the full `d2FlowStageFrontContract` for every concrete candidate
stage. The proper-descendant version of that predicate is also defined, with a
checked lemma that root overwrites preserve it. The root's own 4096 endpoint
residues are now proved to survive every candidate stage; the proof excludes
`botRise` at level zero and uses the all-depth quota divisibility theorem.
2026-10-27 all-depth alignment update: `D2CutAlignment.lean` now
kernel-checks the conversion from the proper-descendant endpoint predicate
plus current root residues to the full ordinary-endpoint predicate. The
coupled state (tile alignment, root endpoint residues, and role-sensitive
descendant endpoint residues) is propagated through each candidate stage at
`t Ã¢â€°Â¥ 1`. The bootstrap stage is handled directly: it resets child endpoints
to zero, and its front contract is automatic because the only active role is
`topDesc`. These results compose to the unconditional all-depth theorems
`d2FlowCandidateRun_frontContract_all` and
`d2FlowCandidateRun_tileAligned_all` for every depth `d Ã¢â€°Â¥ 7`.

This closes the recursive scheduler-to-tile alignment gate; it is not the
rank-transfer recurrence and does not prove that the constructed network
sorts. The global rank-transfer argument, terminal exact sorting, and the
coefficient-300 limsup theorem remain open. The focused Lean check of
`D2CutAlignment.lean` and `git diff --check` pass.

2026-10-27 exact-rank regrouping composition: `D2ColumnRebatchBridge.lean` now proves `fullHeightTwoShuffle_exact_rank_rebinned_l1_le_448`. It composes the fixed tile's checked exact-rank column-port bound (416 core deviation + 32 row-major correction) with the general finite regrouping inequality, so the total absolute error remains at most 448 for any map from refined `(column, port)` cells to receiver groups. A fresh focused Lean check rebuilt `D2RankRebatch`, `D2RowMajorMismatch`, `D2Slope25LiftArea`, and `D2ColumnRebatchBridge` from current sources into ignored `LLM-helpers/sub300-check`; all completed successfully. This is still a local fixed-tile estimate: the actual D2 receiver map must be constructed from scheduled static addresses, then its source rank profiles must be related to reachable flow state. The all-depth global rank invariant, terminal sorting, and coefficient-300 theorem remain open.
The same module proves the budget arithmetic `448/(4096*64) * (279/256) < 1/512`, so if a sender is assembled from complete tiles and its allocation ratio is bounded by `279/256`, the grouped local transfer fits the proposed normalized child-error allowance. Complete-tile decomposition (especially ragged boundaries) and the global profile induction are still not established.

2026-10-27 partial-row preservation gate: `D2LiftedShuffleBridge.lean` now proves `rowShiftLoadByRows_le_of_height_le` and `fullHeightTwoShuffle_le_of_height_le`: if every input column is a prefix of at most `m` rows, both fixed-core shuffles leave every output column with at most `m` false wires. The proof uses that each row-preserving shuffle sends at most one wire per row to each output column. This addresses the profile-level part of the candidate's partial-tile issue: all-one padding rows remain outside the false profile. The exact depth-7 flow audit reports 13 partial-tile sender allocations, all remainders being complete row multiples (32,768 through 196,608), so uniform partial-row tiles are the relevant ragged case. Still missing is the network-level restriction/routing proof that turns this padded fixed-tile profile bound into an execution on the actual sender wires; no global recurrence or sorting conclusion follows.
The partial-row case is now connected to the 448 transfer bound: `D2ColumnRebatchBridge.lean` proves `fullHeightTwoShuffle_partial_rows_rebinned_l1_le_448` for any positive number of ports, any live row height `mÃ¢â€°Â¤4096`, and any receiver grouping. Its proof extends only the final port to row 4096; the profile cap theorem shows that this padding changes neither the actual nor ideal threshold counts. A focused Lean compile of the current `D2ColumnRebatchBridge.lean` passed. This closes the fixed-core *profile* estimate for complete and partial-row tiles, but not the comparator-network restriction to actual sender wires, nor the all-depth flow/profile induction.

2026-10-27 variable-height semantic core: `D2PartialRowBridge.lean` kernel-checks
`rowShiftLoadByRowsM_eq_full` (a live `m`-row shift count equals the fixed
4096-row formula when every profile height is at most `m`), the universal
`rowShiftLoadByRowsM_le`, and the generic column-prefix semantics for one and
two D2 shuffles. In particular, `semanticExec2_two_stride_eq_prefixM` works
for arbitrary `m` and identifies the semantic output with the two successive
`m`-row shift-load transitions. The existing generic `physicalPack2Net_exec`
then supplies the concrete comparator-network execution up to its known
within-row permutation. A direct kernel check of the further theorem equating
the two `m`-row transitions with `fullHeightTwoShuffle` was too expensive in
the initial proof form and was not accepted as checked; that reduction remains
to be factored and verified. Thus this closes the semantic execution part of
the partial-tile bridge, but not yet its fixed-core 448 rebatching interface,
the scheduler-to-receiver address map, the global rank-profile recurrence,
terminal sorting, or the coefficient-300 limsup theorem. The focused
`D2PartialRowBridge.lean` check passes to ignored `LLM-helpers/sub300-check`.
2026-10-27 variable-height semantic core: `D2PartialRowBridge.lean` kernel-checks
`rowShiftLoadByRowsM_eq_full` (a live `m`-row shift count equals the fixed
4096-row formula when every profile height is at most `m`), the universal
`rowShiftLoadByRowsM_le`, and generic column-prefix semantics for one and two
D2 shuffles. `semanticExec2_two_stride_eq_prefixM` works for arbitrary `m`
and identifies the semantic output with the two successive `m`-row shift-load
transitions. The existing generic `physicalPack2Net_exec` connects this
semantic execution to a concrete comparator network up to its known within-row
permutation. The remaining adapter from the two live-row transitions to the
fixed `fullHeightTwoShuffle` profile was attempted separately; Lean's default
heartbeat limit was exceeded, and a higher-budget isolated check was stopped
after several minutes without a result. It is not counted as checked. This
leaves the fixed-core 448 rebatching interface and its actual scheduler address
map open, alongside the all-depth global rank-profile recurrence, terminal
sorting, and coefficient-300 limsup theorem. A focused fresh check of
`D2PartialRowBridge.lean` passes to ignored `LLM-helpers/sub300-check`.

2026-10-27 hard-tail alignment gate: `D2-HARD-TAIL-ALIGNMENT-GATE.md` records
an all-row-dominance LP screen with the optimistic rule that cuts at least 80
rows from the threshold interval have zero local crossings. At depth 5 / scale
128, HiGHS returned a numerically feasible incumbent with `V+E/8` drift
`+18,770.86` in phase 2 (primal residuals below `4e-9`), although its time
limit prevented an optimality proof. The depth-3 / scale-1024 phase-1 gate is
optimal at `-75`. These screens argue against a uniform scalar contraction and
for a phase-dependent/off-spine state; neither is a counterexample to the
fixed network, and neither establishes the hard-tail provider.

The same phase-2 hard-tail gate with flat level weights `w_i=1` also returned
a feasible positive drift, `+30,879.61`, at depth 5 / scale 128, with all-row
dominance and `E/8`; residuals were below `3e-9`. Its cross-bag L1 trace rises
from 608,478 to 638,686, predominantly off-spine. So neither the geometric
nor flat level-only potential is a viable uniform contraction in this
relaxation; a phase/spatial state is needed. Full command and model limits are
recorded in `D2-HARD-TAIL-ALIGNMENT-GATE.md`.
The flat level potential also has a feasible positive two-transition return
drift `+6,600` from stage 2 to stage 4 under the same hard-tail/all-row model.
A hand-chosen frontier-centered level profile likewise has positive
one-step drift; neither screen optimizes over all potential weights. The
next diagnostic should search for a cyclic phase/spine/off-spine weight
certificate or expose a reachable-state condition strong enough to exclude
these witnesses.

2026-10-27 static-address refinement check: `D2StaticWireSets.lean` now proves that slicing a D2 sender by global rank and intersecting with one static destination interval is exactly the union of the per-gap-run fragments (`blockOf_staticHoleList_inter_cell`). A focused Lean check of the module passed. This provides an address-level decomposition but adds no new error bound: `D2RankProfileRouting` already bounds arbitrary groupings of rank errors by 448. The remaining gap is proving that the actual scheduler's next-stage cells are covered by complete/partial fixed-core tiles with the required per-tile source profiles, then applying the global coupled recurrence. The decomposition alone does not establish either fact.

2026-10-27 ordinary-flow address composition: `D2StaticWireSets.lean` now proves `destinationPiece_staticHoleList_child_inter_cell`. For a real ordinary D2 child rank port cut from a parent sender represented as a parent interval minus ordered child holes, the theorem identifies the port's intersection with any static destination interval as exactly its per-gap-run rank fragments. This combines the existing flow rank-port interface with the static sender address model and gives explicit cuts for subsequent tile/column refinement. The focused module check passes. It still does not show that the fixed core's column-port cuts refine this address partition or that their rank profiles satisfy the 448 estimate; those are the next semantic obligations, followed by the all-depth rank/inversion recurrence and terminal cleanup.

2026-10-27 row-major flow-cut conversion: `D2RowMajorFlowCuts.lean` kernel-checks `rowCutAtRank`, the exact equivalence between a per-column prefix and a flattened row-major rank prefix, and `rowMajorFlowCuts_port_contained`. Given any monotone partition of a 4096Ãƒâ€”64 tile's flattened rank interval, the induced per-column row cuts form valid complete ports, and every resulting column-port fragment lies wholly inside its assigned D2 rank interval. This is the needed geometric refinement for applying the fixed-core port estimate with flow-aligned ports. The module passes a focused Lean check. Still to compose: the 448 exact-rank error theorem with these induced cuts and the scheduler's clipped per-tile bounds/tags, then show the resulting rank-profile state obeys the all-depth recurrence and terminal criterion.

2026-10-27 clipped global-flow/core composition: `D2RowMajorFlowCuts.lean` now proves `clippedGlobalFlowPorts_core_error_le_448_per_tile`. Starting from one monotone partition of the full sender's row-major rank interval, it clips every flow boundary to each 64-by-`m` tile, converts those cuts into per-column row cuts, and applies the exact-rank fixed-core provider grouped by the original D2 destination tag. Summed over all tiles, the grouped l1 mismatch is at most `448 * tiles`; this includes partial-row tiles (`m <= 4096`) using the existing all-one padding lemma. A fresh direct Lean build of `D2ColumnRebatchBridge.lean` from source and a fresh kernel check of `D2RowMajorFlowCuts.lean` both passed (using the identical `AKS.Chvatal.ExecPlacement` / `SortedColumnDecode` sources from `upper-bound/best` for the D2 core dependencies). This closes the geometric cut and local-error composition, conditional on the actual sender being tiled in sorted rank order and having the stated live-row profile. It does not yet show how these per-tile errors update the flow-tree's spatial rank state or prove its all-depth contraction; the terminal criterion and coefficient-300 theorem remain open.

2026-10-27 composition audit correction: `clippedGlobalFlowPorts_core_error_le_448_per_tile` is a fixed-core bound relative to each tile's *actual* zero mass. It does not yet include tile-mass misalignment against the global flow's ideal threshold allocation. The existing complete-tile theorem `tiled_global_rank_error_le_parent_add_448_per_tile` supplies that macro-parent correction abstractly, but the new clipped/global-cut construction still needs to be composed with that theorem (and its partial-row extension) before claiming the full flow-stage transfer.

2026-10-27 clipped global-flow parent correction: `D2ClippedFlowRankTransfer.lean` now kernel-checks `clippedFlowTileBoundary_valid` and `clipped_global_flow_rank_transfer`. Given one monotone global rank partition, the theorem clips its boundaries to each fixed 64-by-`m` tile (padding the final boundary through all-one rows), then applies the existing parent-error + 448-per-tile transfer while preserving the global destination tags. A fresh direct Lean check passed. This closes the abstract parent-mass correction for the clipped flow partition; it still assumes the actual scheduler's sender is tiled in sorted rank order with the stated source-height profiles and that its tags match the flow outputs. The concrete stage-to-flow-state identification, all-depth contraction/terminal criterion, and coefficient-300 sorting theorem remain open.

2026-10-27 clipped doubled-budget invariant step: `D2ClippedFlowRankTransfer.lean` now also proves `clipped_global_flow_rank_error_preserves_doubled_budget` and its natural-count form `clipped_global_flow_rank_error_le_next_budget`. For a single global monotone partition clipped across tiles, parent tile-mass error at most `512*tiles` plus the local fixed-core error yields at most `512*outputTiles` when `outputTiles=2*tiles`; the rational normalized error is at most `15/8192`. This handles partial tiles and retains arbitrary receiver tags. The new declarations pass a fresh direct Lean check. This is the quantitative one-stage induction contract. Applying it to the actual comparator network still requires proving that the scheduler's physical stage induces these clipped boundaries/tags and that the next stage's actual tile masses are exactly the modeled receiver counts. The all-depth recurrence, inversion threshold `theta <= 27/301`, terminal cleanup, and limsup bound 300 remain unproved.

2026-10-27 tile-dependent receiver tags and live clipping identity: `D2ClippedFlowRankTransfer.lean` now accepts the actual routing label as a function of both tile and local port (rather than incorrectly assuming one tag per port). It also proves `clippedFlowTileBoundary_live`: after restricting to the live `64*m` positions, every clipped boundary is exactly the translated global boundary clamped to the tile; the padded endpoint intersects the live region exactly as the true global endpoint does. The fresh focused Lean check passes. This repairs the interface needed for tile-straddling receiver groups and gives the exact boundary geometry, but does not identify the D2 schedule's concrete receiver sets with the resulting tile-port groups.

2026-10-27 full spatial-profile local error: new `D2ClippedFlowProfileTransfer.lean` proves `exactRankColumnHeight_sum`, `exactRankColumnHeight_l1_distance`, and `exactRankColumnPorts_distance_le_mass`; splitting two exact rank prefixes into any monotone column-port partition costs at most their original tile-mass discrepancy. It also proves `clipped_global_core_profile_error_le_448_per_tile`: after clipping one global partition into partial tiles and inducing per-column row cuts, the fixed core contributes at most448 l1 error per tile across all 64-column/port cells. A focused direct Lean check passes. This preserves the spatial profile state needed by the global recurrence, unlike the earlier tile-total transfer. Still open: compose parent and local cell errors into the scheduler's true receiver groups, prove those groups match actual D2 next-stage bags, and establish the all-depth inversion/terminal bounds.

2026-10-27 full-profile parent/local composition: `D2ClippedFlowProfileTransfer.lean` now proves `clipped_global_profile_error_le_parent_add_448` and `clipped_global_profile_error_le_next_budget`. For the whole 64-column/port profile, the l1 mismatch after clipped fixed-core tiles is at most the incoming tile-mass error plus448 per tile; the parent term is charged once using the exact-rank column-profile identity and arbitrary row-port partition. Consequently, if output tile count doubles and incoming error is at most512 per tile, the next grouped profile remains within512 per output tile. The complete module passed a fresh direct Lean check. This proves the abstract spatial recurrence step, including partial tiles and arbitrary tile/column/port receiver tags. Still not proved: that the actual D2 comparator schedule induces these tags and ideal masses at every stage, that this recurrence yields the required global inversion exponent, or terminal cleanup and the limsup-300 theorem.

2026-10-27 strict-contraction adversarial gate: reran `coupled_rank_lp.py` at depth5, scale8192, `(3,3,2)`, row bits13, ordered global prefixes, root-tail initialization, 64-row cuts, and the certified width-64 distance-tail profile. With geometric level weights `(1,1/2,1/4,1/8,1/16,1/32)` and local-error weight `1`, the relaxed two-transition potential is nonincreasing to solver tolerance at source phase1 (`max destination-minus-source = 6.5e-8`). However, asking for even `1%` contraction (`rho=0.99`) gives optimal positive destination-minus-`rho`-source growth `8123.72` from phase1 and `76799.69` from phase2 (HiGHS optimal, status0). Thus this LP relaxation does not support a strict contraction theorem for this natural weighted l1 potential, even though the `rho=1` gate can pass. The matching integer model at phase1 timed out after120 seconds without a feasible incumbent, so the obstruction is currently only an optimal fractional-relaxation witness. This is not a counterexample to the fixed D2 network: the relaxation still omits exact cross-stage/core reachability correlations. It does rule out promoting the current relaxed potential screen to the sublinear-inversion invariant; the next gate needs those correlations or a different state/potential. The outputs also retain terminal wrong mass on the order of millions, so nonincrease alone is insufficient for the `theta < 27/301` cleanup target.

2026-10-27 exact-core scaling gate: tried to add the exact Boolean height-two slope-35/slope-25 transition to the coupled alignment model. At depth3/scale64 (32768 wires), the `--all-global-cuts --exact-slope-core` model exhausted memory while converting its equality matrix. At depth3/scale2 (1024 wires), it constructed 9,477 variables, including 4,096 integer variables, but HiGHS hit the 60-second limit with no feasible incumbent. Scale1 is not a valid fixed-tile instance: an active sender has allocation64 while a height-two core tile has width128. These runs provide no adversarial witness; they show the current exact-core/global-cut encoding does not reach even the small multi-stage gate. A scalable recurrence should instead carry the 64 column heights (or equivalent sufficient state) from one fixed-core output directly into the next routed tile, rather than materialize every global wire cut.

2026-10-27 exact-core local-hull contraction gate: on the valid tiny instance depth3/scale2 (1024 wires, row height2, 16 fixed-core tiles over the two transitions), `--exact-slope-core --continuous-slope-core --pairwise-slope-core-hull` solves the phase1-to-2 potential LP optimally. With level weights `(1,1/2,1/4,1/8)`, local-defect weight1, source alignment floor1, and `rho=0.99`, the maximum `destination - rho*source` is `-1.0933333333`; primal equation/inequality residuals are below `6e-13`. The same gate at threshold1/2 is also optimal with maximum `-0.49`. This is a useful contrast with the positive-growth no-core relaxation: exact local comparator hull constraints remove that toy witness. The input/profile state is still fractional globally, the source floor is only1, and this is only one shallow transition. At depth3/scale4 (2048 wires, 32 core tiles), the 60-second solve timed out with a feasible growth value `-0.39` but an upper bound of `7.88`, so it is inconclusive. The next depth4/scale2 model spent several minutes constructing and was interrupted before a solver result, so there is no scaled confirmation. This does not yet establish an all-depth invariant or a global sorting bound.

2026-10-27 physical row-major adapter: D2PhysicalRankRouting.lean now defines literal row-major port counts and proves their grouped exact-rank l1 error is at most 448 for arbitrary monotone per-column port cuts and receiver tags. Cellwise, each physical count equals the existing prefix-interval mass, so this is a direct wire-count formulation of the fixed-core certificate. Fresh direct Lean check passed (LEAN_EXIT=0). This remains a one-tile certificate; the actual D2 schedule's cuts/tags, all-depth inversion recurrence, terminal cleanup, and coefficient-300 theorem remain open.

2026-10-28 inversion localization formalization: D2InversionLocalization.lean kernel-checks that a misplaced one before the zero-count cut forces at least its cut-distance in inversions, while a misplaced zero at/after the cut forces distance-plus-one. Consequently, if total inversions are at most I, every misplaced zero is in [q,q+I) and every misplaced one satisfies q <= p+I, where q is the exact zero count. This formalizes the localization step used by the fixed cleanup recurrence; it does not prove the needed all-depth inv <= n^theta bound or the cleanup network/depth theorem.

2026-10-28 quadratic cleanup support gate: D2InversionLocalization.lean now also proves cut_wrong_pair_count_le_inversions: for any cut q, the number of one-before-cut/zero-at-or-after-cut pairs is at most the inversion count, since each is a distinct inversion. At the true zero-count cut the two wrong-side populations should agree, giving m^2 <= inv and only 2m wires to repair; that equal-population bridge and a quantitative cleanup network are still unproved. Fresh direct Lean check passed (LEAN_EXIT=0). No global D2 inversion recurrence or limsup-300 result follows yet.

2026-10-28 exact cut-mass bridge: D2InversionLocalization.lean now proves wrong_populations_equal at the exact zero-count cut and hence wrong_population_square_le_inversions: if m is the number of misplaced ones, m^2 <= inv. The new equal-count proof uses only prefix cardinality and conservation of zero mass. Important limitation: this bounds the number of wrong wires, not their positional span; the existing fixed cleanup still pays for the inversion-width interval, so this alone does not lower theta or close the coefficient gate. A sparse-position-independent fixed cleanup network would be a separate required result. Fresh direct Lean check passed (LEAN_EXIT=0).

2026-10-28 higher-moment localization interface: D2InversionLocalization.lean defines the order-s distance moment around a cut and proves each misplaced wire contributes its distance^s to that aggregate. At the exact zero-count cut this is the formal bridge needed to turn an all-depth M_s bound into a radius bound; combined with the existing chunk/seam cleanup, a radius exponent below27/301 is sufficient for the conditional p=273 coefficient-300 route. Fresh direct Lean check passed (LEAN_EXIT=0). This adds no recurrence estimate: the actual D2 schedule still lacks a fixed-provider all-depth bound on M_s, and the finite input-dependent oracle traces are not proofs.

2026-10-28 depth-100 higher-moment screen: added moment_gate_screen.py to reproduce the sparse ordered rank-core oracle diagnostic. For (3,3,2), row height8192, scale8192, threshold1/3, root error fraction10^-30, and initial threshold band, all285 active transitions complete without a modeled capacity failure. At terminal, all non-threshold native blocks are pure and the mixed block has3680 wrong wires. The measured terminal radius exponents are log_N(M1)=0.0693003, log_N(M2)/2=0.0510407, log_N(M3)/3=0.0451352; plugging the last into (273+theta)/(1-theta) gives285.952. This is a promising parameter margin, but each local output is selected by an input-dependent oracle and the initial band is assumed, so neither the uniform moment estimate nor a fixed provider is established. Reproduction: python upper-bound/experiments/prefix-flux/moment_gate_screen.py --depth 100 (about34 seconds).
The same depth-100 screen also passes for initial=outer,left,right (same provider-oracle parameters): terminal wrong counts in the mixed native block are respectively 3680, 2732, 2732; all wholly colored native blocks are pure. Their M3 radius exponents are respectively 0.0481932, 0.0454844, 0.0444733, giving conditional coefficient screens 286.874, 286.057, 285.753. These four distinct starts strengthen the empirical margin but do not address arbitrary initial profiles; the root band sizes remain assumed and the oracle output choices remain input-dependent.

2026-10-28 root-localization stress: reran the depth-100 screen with a much larger initial error fraction10^-3. A centered threshold band still completes: terminal M3 radius exponent0.0440414, mixed-block wrong count3080, conditional coefficient285.623. With the same error mass placed at the left endpoint (initial=left), the ordered oracle fails its necessary future-capacity gate immediately at stage2 on node(level1,index0): wrong mass is about7.86 times its remaining upward escape capacity. moment_gate_screen.py now reports such failure nodes instead of throwing. This isolates a concrete root obligation: low total error or even a successful centered-band trace is insufficient; the root must force spatially localized errors (or the recurrence must retain their distance profile). This is still an oracle diagnostic, not a fixed-network counterexample.

2026-10-28 deterministic two-grid band-repair gate: D2-TWO-GRID-BAND-REPAIR.md specifies a fixed per-column network sorting aligned 64-row bands, then 32-shifted 64-row bands. On any Boolean word that is all ones before a dirty interval and all zeros after it, with interval width at most32, the two layers sort the whole word: after the aligned pass any remaining inversion is confined to32 positions on either side of the unique crossed boundary, which lies inside one shifted segment. Each layer costs at most21 bitonic comparator levels, total42 independent of column height. The fixed D2 profile theorem gives range13, so this local lemma has width slack if its physical stage interface is established. and_repair_screen.py passed127,741 exhaustive cases through width8 plus100,000 random cases through width32 at n=256. Still missing: the network-level Lean realization in this branch, proof that the actual D2 output has exactly this row-band form at the correct point, and the global port/rank recurrence. No full sorting bound is claimed.
### Two-grid band-repair screen (2026-10-28)

The fixed two-grid Boolean-word argument in `D2-TWO-GRID-BAND-REPAIR.md`
requires height divisible by 64. The screen now enforces this precondition;
for arbitrary heights the fitting-segment implementation has a tail
counterexample (height 65, with 64 leading ones and a final zero). At height
4096, a width-13 band from `fullHeightTwoShuffle_range_le_thirteen` would fit
the lemma's width-32 hypothesis if it can be shown to describe the actual
post-shuffle matrix. The current theorem is only about the scalar height
profile. Still required: a 4096-by-64 physical schedule bridge showing the
range bound makes all rows outside one 13-row band uniform across columns,
that the row-preserving shuffle retains this property, and that the aligned
and shifted 64-row segment-sort grids are inserted and charged in the real
network. The Python screen passed 127,741 exhaustive width-at-most-8 words
and 100,000 random width-at-most-32 words at height 256; this is a finite
diagnostic, not a formal network theorem.

### Two-grid Lean progress (2026-10-28)

`D2BandRepair4096Network.lean` now defines both fixed grids on the actual
4096-by-64 wires. Each has depth at most 21, and their composition has depth at
most 42. It proves that every threshold word with dirty-band width at most 32
is sorted by this composition. The file also states the direct composition
with `fullHeightAfterRowPermutation` and the range-13 physical band interface,
so that theorem establishes sorted columns after the row-preserving
permutation. A focused Lean check of the final source now passes, including
this physical composition, after appending the existing `prefix-flux` provider
directory to `LEAN_PATH`. This only addresses a possible replacement for the
third 4096-wire column sort.
The all-depth port/rank recurrence, root treatment, terminal cleanup, and
end-to-end depth accounting needed for coefficient 300 remain open.

The same module now proves an exact profile transfer. It establishes that the
two-grid network is column-local, applies the existing generic theorem that
column-local comparator networks preserve per-column true-counts, and identifies
each repaired output column as the bottom-unary profile with the corresponding
pre-repair scrambled row-sum. It further identifies the resulting 64-height
transition with the existing scrambledColSum operator, specialized to the
affine slope-25 row shuffle used in the physical D2 module. The updated
theorem passes a focused Lean check. Thus the local stage now has an exact
deterministic profile transition in the same representation as the existing
D2 profile lemmas. A further Lean theorem proves that these output heights
still have pairwise range at most 13 after any row-preserving permutation:
the common false exterior bounds each height above, and the common true
exterior bounds it below. This gives a recursively reusable local range
invariant for the fixed stage. This turn packages the exact transition as
`d2LocalProfileStep` and proves by induction that every positive iterate again
has range at most 13 (and stays within the 4096-row domain). This is an
all-depth scalar-profile invariant. A further theorem packages the geometric
meaning: for every threshold, the repaired 4096-by-64 output is constant
outside one common dirty interval of at most 13 rows, i.e. 832 contiguous
row-major wires. This makes a fixed-size terminal sorter locally sufficient
once the global schedule proves that only bounded seam errors remain. It does
not itself bound those seams: the all-depth global rank/inversion recurrence,
root treatment, terminal seam criterion, and end-to-end depth accounting
remain open.
2026-10-28 fixed-core aggregate inversion provider: D2BandInversion.lean proves that every inversion of a Boolean word uniform outside a band lies within the band, giving at most W^2 inversion pairs. D2BandRepairInversion.lean composes this with the existing physical 832-wire common-band theorem for the two-grid repair, yielding inv <= 692224 per threshold and fixed sender, independent of profile size. Both focused Lean modules pass. This closes only a local aggregate provider candidate; cross-sender alignment, seam charging, recurrence initialization, and terminal cleanup remain open.
The same work now strengthens the local conclusion beyond the coarse inversion cap: `physical_twoGridRepair_misplaced_bits_within_832` proves every misplaced threshold bit is within 832 ranks of that fixed sender's exact zero-count cut. The physical common-band interface now carries bounded endpoints so the count cut is formally shown to lie inside the band. This is a local contract only; no theorem yet relates that cut to the correct global rank as sender bags are routed across stages.
The local provider now also has `physical_twoGridRepair_wrong_population_le_832`: at each threshold, at most 832 wires are misplaced relative to one sender's exact zero-count cut. Together with the 832-rank localization, this is a fixed sparse-error contract for each repaired sender. It remains local and does not establish how errors combine under the actual next-stage receiver map.

2026-10-28 sparse mixed-tile transfer interface: `D2SparseMixedTileTransfer.lean` kernel-checks the arithmetic lemma `sum_error_le_parent_error_add_single_mixed`. If each tile's output mismatch is bounded by its incoming target-count mismatch, plus `W` only when its target interval contains the global threshold cut, then a partition with at most one such mixed tile has total output mismatch at most total incoming mismatch plus `W`. This suggests charging the local 832-wire repair once per global threshold rather than once per tile. The focused Lean check passed (`lake env lean` in `upper-bound/best`, with the prefix-flux provider path in `LEAN_PATH`). The current lemma is only the sum interface: proving its per-tile hypotheses from the fixed repair and proving that the actual D2 active tiles form a rank-ordered partition remain open. In particular, this does not yet bound positional displacement or terminal inversions.

2026-10-28 fixed-core Hamming transfer: `D2BandRepairInversion.lean` now proves the two-grid output differs in at most 832 positions from the sorted threshold word with the same zero count, and comparator-network semantics preserves that zero count. `D2SparseMixedTileTransfer.lean` combines this with the unique-mixed-interval fact to prove that over any full-sized rank-ordered tile partition, total post-repair Hamming mismatch is at most incoming tile-count mismatch plus 832. A fresh Lean build of the module into `upper-bound/best/.lake/build/lib/lean` passed. This avoids paying 832 per tile for one threshold. It still assumes full 4096-by-64 tiles arranged in rank order and does not bound positional distance or inversions; connecting the actual scheduled tile map, handling partial tiles, and proving the multi-stage spatial recurrence remain open.

2026-10-28 sender-set displacement lemma: `D2BlockSortDisplacement.lean` kernel-checks that exact sorting an arbitrary, possibly noncontiguous sender preserves an incoming pointwise displacement bound when its physical addresses are listed in increasing order; an approximate sort adds its local error `D`. `D2RankDisplacementComposition.lean` composes uniform per-stage crossing bounds over an arbitrary finite stage list. Focused Lean checks pass. The intended payoff is an additive `O(log n)` rank-displacement invariant followed by sublinear terminal cleanup. The actual per-sender pointwise provider and the subsequent rank-slice routing into next-stage address sets remain unproved, so this is not an end-to-end upper bound.
Correction to the preceding status note: `partitioned_sender_stage_adds_error` is now also kernel-checked in `D2BlockSortDisplacement.lean`. Given a current owner/slot decoder for every physical wire, it combines all sender-local bounds into a whole-stage `E+D` displacement bound. Reassigning an existing address to its next-stage owner adds no separate displacement charge. The actual D2 decoder and, especially, the required uniform local pointwise error relative to exact sender sorting are still open.

2026-10-28 local D2 third-moment packaging: D2BandRepairMoment.lean kernel-checks physical_twoGridRepair_third_moment_le_832_pow_four. The existing physical two-grid provider has at most 832 wrong-side wires and places each within 832 ranks of that sender's exact zero-count cut, hence its local M3 is at most 832^4 uniformly over all height profiles. This supplies a reusable local moment contract; it does not move the center to the global rank cut or bound the sum across senders. Fresh focused Lean check passed (LEAN_EXIT=0).

2026-10-28 rank-displacement route: `D2BlockSortDisplacement.lean` now kernel-checks `localized_threshold_errors_give_pointwise_rank_displacement`. If a local comparator network's threshold errors are confined to a width-`W` band around every threshold, then each key's output position differs from its exact rank by at most `W` (use thresholds `r` and `r+1`). Combined with `partitioned_sender_stage_adds_error`, a per-sender bound of 832 would give global displacement at most 832 times the number of active stages. A fixed block/seam cleanup for an `O(log n)` dirty band costs `o(log n)`, so this route preserves the prefix-stage coefficient, conditionally 273 for the `(3,3,2)` candidate. Still open: transfer the physical Boolean band provider to arbitrary-key ranks through the complete local network, instantiate the actual scheduled sender partition at every stage, prove the all-depth stage count/depth, and give the fixed cleanup construction its exact bound. The local Hamming bound alone is insufficient; the proof must use the stronger localized-threshold theorem.

Reuse found during the same investigation: `D2PointwiseRankError.semanticExec2_two_stride_rank_displacement` already proves a 3392 pointwise rank bound for the semantic two-stride core on column-monotone permutation inputs. This may be the shortest local-provider route: identify the scheduled sender network with that executor after its first column sort, then feed the result to the existing arbitrary-sender displacement composition. Do not assume this matches `twoGridRepair` or the full scheduler until the network/address equivalences are checked.

The conditional physical-core bridge is now kernel checked as `physical_twoGrid_threshold_family_rank_displacement` in `D2BandRepairInversion.lean`: a permutation-valued output has displacement at most 832 if each of its rank thresholds is exactly the fixed two-grid output for some bounded height profile and the same row permutation. The proof obtains the threshold zero count from bijectivity, then applies the existing localized-bit theorem and the new generic implication. This isolates the remaining local task precisely as proving that threshold-family equation for the actual preceding column-sort/two-shuffle/routing network; the theorem does not assume or prove that equation.

2026-10-28 fixed-core pointwise rank bridge: `D2LocalRankDisplacement.lean` now kernel-checks `localCore_rank_displacement`. Given a permutation-valued key layout descending within each 4096-wire column, the fixed two-shuffle, rowwise column permutation, and two-grid repair macro moves every key by at most 832 wire ranks. The proof thresholds arbitrary key ranks, uses threshold commutation through comparator networks, applies the exact full-height profile transition, and invokes the existing physical band-repair theorem. The rowwise permutation is oriented to match `fullHeightAfterRowPermutation`; an earlier inverse convention did not match that provider. Focused Lean check passed from `upper-bound/best` with the prefix-flux provider directory appended to `LEAN_PATH` (`lean -o ..\experiments\prefix-flux\D2LocalRankDisplacement.olean D2LocalRankDisplacement.lean`). This is a local map theorem only: its input monotonicity convention, embedding into every actual sender, aggregate schedule depth, all-depth rank/port recurrence, terminal cleanup, and the limsup statement remain unproved.
The local rank bridge also proves `localCore_restores_columnMonotone`: the fixed macro sends every descending-column permutation input to an output whose key ranks are ascending down each column. This is the direction flip required by the exact 0/1 threshold proof, so the next sender interface must explicitly account for the D2 stage's row/orientation mapping; the local theorem alone does not provide an iterated sender invariant.

2026-10-28 sharpened clipped rank-error recurrence: `D2ClippedFlowRankTransfer.lean` now proves `clipped_global_flow_rank_error_preserves_448_budget` and its abstract all-depth iteration `doubled_rank_error_recurrence_le_448`. Under the transfer's hypotheses (rank-ordered input tiles, monotone global cuts, output tags, and doubled tile count), parent error at most448 per tile plus the fresh448-per-old-tile core error yields exactly448 per new tile at every depth. A focused rebuild passed. This closes the error arithmetic, but does not produce the actual D2 sender tags/cuts or prove that their parent errors are the previous stage's output errors; the limsup bound remains unproved.

2026-10-28 local-core realization gate: `D2Slope35Physical4096.lean` now kernel-checks `reorientWirePerm_reverses_column_rows`: the profile reorientation sends increasing rows in a fixed column to decreasing physical rows. Consequently the existing order-preserving `relabelNet` lemma cannot directly realize the intervening reorientation around an ascending column sort; a valid network-level bridge must account for comparator direction or absorb this reorientation into the preceding/following scheduled wiring. The focused module check passed. This narrows the missing local-core-to-network proof and reinforces that the 832 displacement theorem is currently semantic, not yet a sorting-network stage theorem.

2026-10-28 physical two-round alternative: `D2TwoStrideArbitraryRank.lean` proves the existing3392 semantic displacement estimate for every permutation input by using the executor's own first column sort to establish column monotonicity. `D2PhysicalRankReindex.lean` proves that the physical pack's cumulative row-preserving output permutation adds at most63 wires. `D2PhysicalPackRankDisplacement.lean` combines these with `physicalPack2Net_exec` and kernel-checks a 3455 pointwise displacement bound for the actual fixed physical comparator network. The focused checks for all three modules pass. This resolves the local orientation/realization gate for the un-repaired two-round pack, but the all-depth sender-address/rank recurrence and its integration with the candidate 273 depth schedule remain open; the limsup bound is not yet proved.

2026-10-28 arbitrary-key sender normalization: `D2PhysicalSenderRankDisplacement.lean` composes the 3455 physical-pack estimate with `NodeKeys.exec_rankPerm`. For any injective list of global keys occupying all 4096-by-64 sender slots, the actual physical network leaves each key's rank *within that sender* within 3455 of its output slot. This is the right local statement for an approximate-sender-sort recurrence and removes the full-permutation-values restriction. The focused Lean check passes. The actual D2 schedule still has to realize these fixed-size sender partitions, and its receiver readdressing, all-depth transition, prefix depth, and terminal cleanup remain unproved.

The same module now proves `physical_sender_adds_gap_scaled_rank_error`: if sender slots are ordered physical addresses and their address map has gap growth at most `G` per slot, the fixed network increases the global pointwise rank-displacement envelope by at most `3455*G`. This composes the arbitrary-key local theorem with the existing finite-order counting argument in `D2BlockSortDisplacement.lean`. The focused check passes. Applying it to the D2 schedule requires a uniform small gap bound for every actual sender (including hole-spanning senders); no such all-stage bound is established, and a large `G` would make the estimate useless for a 300 coefficient.

2026-10-28 arbitrary-root quotient correction: `d2_port_quotient_lp.py` had
fixed every root prefix to the already-sorted profile, invalidating its prior
arbitrary-input interpretation. The default now preserves exact total root
threshold mass while allowing each root local prefix to vary under the
modeled prefix bounds. Their transfer to the actual D2 core remains open.
With the corrected width-64 tail profile at
depth5/scale8192, the exact quotient LP has 2,477 classes and solves to
4,376,781.515 summed nested-terminal wrong mass (maximum equality residual
1.40e-9 and inequality violation 2.14e-9), versus 1,882,883.515 with a
sorted root. The arbitrary-root depth2 objective is 6,390.0192, matching the
previous root-tail gate. This is a relaxation witness, not a fixed-network
counterexample; it shows that these local tail constraints still leave large
global alignment freedom. At depth6 the arbitrary-root run has the same2,477
classes and yields35,028,192.118 summed nested-terminal wrong mass; the
sorted-root depth2 compatibility check matches the raw LP to below3e-11.
Reproduction and caveats are in
`D2-DISTANCE-TAIL-PERIOD-GATE.md`.

2026-10-29 Stage-14 flow-state checkpoint: the scratch modules
`D2Stage14*.lean` culminate in `D2Stage14PreservesInv.lean`, whose theorem
`d2FlowCandidateStage14_preserves_inv` proves the actual recursive flow-tree
invariant through stage 14 for every child depth at least 7. The existing
compiled artifact postdates its source, and an import check confirms the
declaration. This extends the checked finite prefix but does not establish a
uniform arbitrary-stage induction; all later sender-cap and endpoint-reserve
obligations, global rank transfer, terminal sorting, and the coefficient-300
limsup theorem remain open.

2026-10-29 local port-label refinement: `D2RankCutSeamBound.lean` now proves
`portLabel_mismatches_le_crossers`, converting differing physical-slot and
sender-rank labels into at least one crossed seam, and composes it with the
fixed-core bound to obtain at most 14,985 mislabelled slots across an ordinary
sender's nine seams. The focused Lean check passes. This is a local counting
interface only; it does not replace the existing `D2RankProfileRouting`
arbitrary regrouping theorem or close the all-depth scheduler-to-profile
recurrence. The naive alternative of charging raw physical hole lengths has a
finite screen growing roughly quadratically in schedule depth.

Follow-up gate on the absolute seam route: nine seams and 832 pointwise local
rank displacement give at most 14,985 mislabelled slots per 262,144-wire
sender, hence at most 29,970 l1 error for a Boolean receiver histogram by the
two-endpoint-per-mislabel estimate. This is far above the 512 fresh-error
allowance per sender needed by the doubled profile recurrence. The existing
448 local rank-profile provider is much sharper; therefore the seam estimate
does not replace it. Keep the seam theorem only as a local combinatorial
bound, and focus on instantiating the 448 provider with actual scheduler tags
and proving the all-depth flow-state invariant.

2026-10-29 physical local-provider correction: the actual row-dependent
permutation plus two-grid repair has output column-count range at most13, by
the 832-wire common-band theorem and column monotonicity
(`reflectedPhysicalPackTwoGrid_columnCount_range_le_13`). A generic checked
zero-sum l1 lemma then gives 448 against the exact rank profile, and
`D2PhysicalProfileRangeTransfer.lean` lifts this to arbitrary monotone
per-column port cuts, with error summed over all individual column/port cells.
Both focused direct Lean checks pass. This closes the physical local 448
provider gap for complete 4096-row cores. It does not yet instantiate clipped
partial-row outputs, identify every actual scheduled receiver tag with these
cells at every stage, prove the global inversion/moment recurrence, or prove
terminal cleanup.

2026-10-29 physical-to-clipped profile bridge: `D2PhysicalProfileGlobalTransfer.lean`
now kernel-checks `physicalCore_clipped_cells_error_le_448` and
`physicalCore_grouped_profile_error_le_parent_add_448`. The first applies the
physical 448 l1 provider to actual clipped cells induced by any global
monotone rank partition. The second composes this with the existing arbitrary
receiver-tag theorem, yielding grouped error at most incoming tile-mass error
plus 448 per complete 4096-row tile. A generic port-partition lemma was added
to `D2PhysicalProfileRangeTransfer.lean` so this composition keeps the concrete
comparator net opaque during transfer. Focused direct Lean compilation of
both changed modules passes. This closes the local physical-provider to
clipped-cell interface for full tiles; it still assumes global monotone cuts,
a tile-mass parent-error bound, and receiver tags. The actual recursive
scheduler has not yet been proved to supply these hypotheses at every stage;
its all-depth invariant, depth accounting, terminal cleanup, and the
coefficient-300 theorem remain open.

2026-10-29 independent-cut transfer and scheduler audit: the same module now
kernel-checks `physicalCore_variable_column_error_le_parent_add_448`. It
allows different monotone row cuts for every column of every tile, groups
those cells under arbitrary receiver tags, and charges only aggregate parent
mass error plus 448 per input tile. This is the schedule-facing form of the
physical provider. Separately, current-source compilation of
`D2CutAlignment.lean` confirms `d2FlowCandidateRun_alignment_all` and
`d2FlowCandidateRun_frontContract_all` hold for every positive stage; the
sender-boundary grid theorem in `D2VariableTilePhysicalFlowTransfer.lean`
still assumes recursive `d2FlowStageInvInputs` at that stage. Thus the next
schedule proof obligation is the all-stage sender cap, allocation, parity,
and endpoint-reserve contract, not geometric alignment. The exact
`d2_reachable_reserve_audit.py --depth 250` run was stopped after more than two
minutes without output; this gives no pass/fail evidence and should not be
repeated at that depth without optimizing the FlowDAG enumeration.

2026-10-29 stronger ordinary-sender deficit envelope: the new
`D2StrongDeficitPropagation.lean` kernel-checks a one-update estimate under
the sharper parent condition `G = 0` with `256*pi <= c`, or
`8192*G + 7 <= 15*c` with `4096*pi <= 15*c`. The endpoint child deficits
then satisfy the same affine envelope at capacity `2*c`; six interior child
deficits reset to zero. This is strictly sharper than the `23/4096` tolerant
gate used by the current all-stage transfer. The revised reserve audit at
depth 100 passes every local input check for 204,348 active ordinary senders
across 744,031 states. Its maximum deficit is exactly `15/8192 - 7/c` at
`(stage 215, level 73, botDesc)`; the minimum normalized affine slack is
`7/c` at that same sender, and quota, allocation, parity, and endpoint
reserves also pass. These remain finite diagnostics: the next proof gap is
to establish the sharp profile and the other sender-input fields for every
stage by induction (with a proved startup case), then connect that contract
to the already checked schedule transfer. The depth-100 run took about 16
seconds. No all-stage invariant or coefficient-300 theorem is claimed.

The same module now also proves the bridge needed to reuse the old stage
interface: the sharp parent profile implies its `512*G <= c` and
`256*pi <= c` local caps, and the sharp one-step output implies
`512*G_child <= 2*c` at the next scheduled capacity. Focused direct
compilation of `D2StrongDeficitPropagation.lean` passes after these additions.
This removes a local interface mismatch; it does not supply the all-stage
profile induction or prove the remaining allocation, parity, and reserve
fields.

2026-10-29 Stage-15 schedule interface: the new `D2Stage15Frontier.lean`
kernel-checks the post-Stage-14 activation and role split. At stage 15, the
active-level set is exactly {1, 3, 5, 7}; levels 3 and 5 are mid senders and level
7 is bot-rise. The top level 1 is top-descending for `d = 14` and top-rising
for `d >= 15`, because the rounded top frontier behaves differently at that
single threshold. This gives the exact role cases for a Stage-15 input proof;
it does not yet prove any Stage-15 sender input or extend the all-stage
invariant.

The Stage-14-to-15 child transfer has reusable generic pieces already in
`D2ScheduleReserve.lean`: `d2FlowStage_regular_child_balanced` gives the
post-cut child's balance equation, `d2_regular_update_preserves_child_g_bound`
propagates `512*G <= c` to `512*G_child <= 2*c`, and
`d2FlowCandidateCapacity_succ_level_next_stage` identifies that doubled
capacity with the next level/stage schedule. Thus a Stage-15 proof should
reuse these for balance and deficit. The unresolved actual-input work is
allocation and endpoint reserves for levels 3 and 5 after stage-14 recursive
updates, plus checking the exceptional level-1 branch. The existing
Stage-14 preservation artifact imports and exposes its theorem, but its source
was not freshly rebuilt in this turn.

Stage-15 endpoint-reserve arithmetic is now formalized in
`D2Stage15Frontier.lean`. For every `d >= 14`, the Stage-14 level `i+1`
capacity is exactly 32 times the Stage-15 level `i` capacity, and a
mid/bot-descending quota is exactly `15/4096` of the larger capacity. Since
`d2FlowStage_active_node_deficit` says the active Stage-14 sender adds this
quota to its root deficit, that local output alone supplies the Stage-15
`1/128` reserve. The theorem is composed with the actual local D2 stage
transition and kernel-checks. The schedule role split is also proved:
Stage-14 levels 4 and 6 are active, with roles mid and bot-descending. The
specialized local transfer theorems show that the Stage-14 output at level 4
supplies the Stage-15 level-3 reserve and the level-6 output supplies the
Stage-15 level-5 reserve. To use them for the global Stage-15 input proof,
one still needs to identify the actual level-4/6 roots in the fully staged
run with these local transitions and prove the allocation inequalities at
levels 3/5.

2026-10-29 actual Stage-15 endpoint reserves: `D2Stage15ActualReserves.lean` now
kernel-checks the four-edge and six-edge inactive-ancestor projections and
composes them with the actual candidate run. For every branch, the Stage-15
level-three and level-five roots are identified with the local Stage-14
level-four/six sender outputs; the existing local reserve bounds then prove
both actual endpoint reserves. The focused direct Lean compile passes. This
closes the Stage-15 endpoint-reserve fields for its two ordinary mid senders;
it does not establish their allocation bounds, the exceptional top sender, the
full Stage-15 input invariant, or an all-stage induction. The coefficient-300
claim remains unproved.

2026-10-29 Stage-15 allocation refinement: `D2Stage15ActualReserves.lean`
now also kernel-checks the local eight-child aggregate step and the schedule
arithmetic. At Stage 14, each active level-four mid quota is exactly 32 times
the next Stage-15 level-three quota. Therefore eight such fresh child quotas
more than fund the next quota whenever the Stage-15 root deficit is at most
its scheduled capacity divided by 512. This is an allocation interface, not
yet the actual Stage-15 allocation proof: the active Stage-14 level-two cut
rewrites the level-three root, and that parent-cut output must still be shown
to satisfy the required cap in the actual run. The local inactive-parent
aggregate theorem applies only when the level-three root itself is preserved.


2026-10-29 Stage-15 level-three parent cap and allocation: `D2Stage14ActualLevelTwoChildAdapter.lean`
exports the actual Stage-14 level-two input contract at a nested-child path,
and `D2Stage15LevelThreeRootCap.lean` kernel-checks the actual Stage-15
level-three root bound `512 * G <= capacity(d, 3, 15)` for every branch and
`d >= 14`. `D2Stage15ActualReserves.lean` now also kernel-checks the complete
Stage-15 level-three allocation field. Each of its eight level-four children
is itself an active Stage-14 level-four sender, so its root receives the fresh
mid quota. The exact quota ratio makes eight such quotas sufficient for both
the Stage-15 quota and its root deficit under the proved `1/512` cap. The
module compiles with all additions.

The quota-floor argument applies to these level-four roots. It does not imply
that every level-five child of a level-four sender receives a quota; the
ordinary-cut profile can clear interior roots. No all-stage invariant or
coefficient-300 theorem is established by these Stage-15 lemmas.


2026-10-29 actual Stage-15 level-five root cap: `D2Stage15LevelFourInvariant.lean`
proves that the Stage-13 invariant descends to every actual level-four sender
entering Stage 14. `D2Stage15LevelFiveRootCap.lean` then kernel-checks
`512 * G <= capacity(d, 5, 15)` for every actual Stage-15 level-five child
root, using the Stage-14 level-four input contract and ordinary-child bound.
Both focused Lean commands completed successfully. This adds one field for
Stage 15 only; the full Stage-15 invariant and the all-stage rank recurrence
are still open, so it does not establish the coefficient-300 bound.


2026-10-29 actual Stage-15 level-five allocation: `D2Stage15LevelFiveAllocation.lean`
kernel-checks the Stage-14 level-six bottom-descending child quota floor, its
exact 32-to-1 relation with the Stage-15 level-five middle quota, and the
complete actual Stage-15 level-five allocation field. It composes with the
level-five root-cap lemma. This closes these two local fields for that sender
level; it does not prove a complete Stage-15 invariant or the global
rank-profile recurrence needed for the coefficient-300 result.

2026-10-29 propagated-tail recurrence screen: `coupled_rank_lp.py` now allows
the pointwise whole-tail constraint on a row grid (`--row-stride`) and groups
mass selectors into bins of that same gap (`--propagated-tail-gap`), giving a
sound weaker relaxation than imposing every row cut. At row height 8192,
depth 2, schedule `(3,3,2)`, stride/gap 64, and the exact internal
`profile_tail` provider, the selector-MILP solved optimally with terminal wrong
mass 5951. Adding 1816 distance-tail inequalities from the UB-34
`cert_walk_n.py` margin values at 512, 1024, 2048, 4096, and 8192 rows reduced
the optimum to 4430.96. These solutions still allow fractional wire profiles;
they are adversarial relaxations, not traces of the candidate network. The
UB-34 margin certificate also has not been proved to provide the same local
contract for this D2 transition, so that augmented run is only a diagnostic.
Stride 32 produced 1,200,853 variables and 3,588,075 inequalities but did not
solve within 120 seconds. The tail-profile route, in its current form, does
not close the global recurrence; tightening its sampled version alone is not
yet a promising next proof step. The separately compiled Stage-15 local
invariant fields above remain useful, but no all-stage rank-profile
contraction or coefficient-300 theorem is established.

2026-10-29 Stage-15 level-seven balance: `D2Stage15LevelSevenBalance.lean`
kernel-checks a data-level seven-edge stage projection and uses it to show
that every actual level-seven root after stage 15 has balanced low/high
endpoints. The cause is concrete: its stage-14 level-six parent is an active
bot-descending sender, whose cut writes balanced root data into each child.
The module also packages the generic constructor that turns this balance plus
inactive descendants into the `botRise` stage-input field. This closes one
more actual Stage-15 field but does not prove all Stage-15 inputs, an
all-stage invariant, the rank-profile recurrence, or the coefficient-300
bound.

2026-10-30 Stage-15 level-one local fields: `D2Stage15LevelOneContract.lean`
kernel-checks the generic `topRise` input constructor, exact schedule quota
arithmetic, and two actual-tree transfer facts. Stage 14's root `topDesc`
resets every actual level-one child's root data to `(0,0,0)`. Projecting two
levels through Stage 14 isolates the active level-two `mid` cut, so every
actual Stage-15 level-two child root receives at least that cut's fresh quota.
The exact ratio is `15/128` of the Stage-15 level-one capacity; eight such
quotas cover its top-rise quota, one supplies each endpoint reserve, and the
Stage-15 quota is even. The full recursive `d2FlowStageInvInputs` assembly at
level one remains open because its level-two child contracts have not yet
been assembled. No all-stage recurrence or coefficient-300 theorem follows
from these local fields.

2026-10-30 Ordinary-cut endpoint-only child profile: `D2OneSidedChildProfile.lean`
kernel-checks a generic reserve lemma and its actual `d2FlowStage` projection.
Under the ordinary-cut reserve hypotheses, child 0 stores only low-side fresh
data, child 7 only high-side fresh data, and all six interior children store
zero root data. This gives the precise reset shape needed to apply the
one-sided rank-cut tail bounds to the next sender. The reserve hypotheses
still need to be established uniformly for every active sender, and this
profile alone does not prove contraction of the global rank/alignment state
or the limsup coefficient-300 bound.

The same module now composes that profile with `rankCutTail_one_sided_le`:
for every regular-stage child, the two tails formed from its stored low/high
fields pay one error allowance plus their combined mass beyond the protected
margin. This is a checked flow-scalar inequality only. The crucial missing
semantic step remains proving that the actual key-rank outsider counts satisfy
these stored flow-field bounds; the flow tree alone does not encode keys.

2026-10-30 D2 two-grid Boolean provider audit: `D2PhysicalPackTwoGrid.lean`
prices the actual reflected pack plus two-grid repair at 276 layers, and
`D2ReflectedPhysicalPack.lean` proves a common Boolean dirty band of at most
832 wires for every input while restoring column monotonicity. At the
candidate 5/6 schedule rate this gives a conditional local coefficient 230,
leaving 70 for routing and cleanup. This supports pursuing the all-depth
proof in Boolean threshold profiles rather than first extracting a
value-level displacement theorem. A generic `exec_comp_monotone` attempt on
the flattened physical network exhausted about 8.6 GB without completing and
was stopped; its incomplete draft was removed. The actual-sender address
adapter, global profile recurrence, and terminal criterion remain open.

2026-10-30 checked sender rank adapter: `D2SenderRankBridge.lean` proves
the generic bridge from a rank-displacement estimate on a comparator network
to global displacement on an arbitrary strictly ordered sender subset. The
inverse rank permutation is shown sorted by a strict finite-set rank argument;
the address-gap lemma then gives the explicit cost `E + L*G`, where `L` is
local rank displacement and `G` bounds the global address increase per sender
slot. `D2PhysicalSenderRankDisplacement.lean` instantiates it with the fixed
4096-by-64 physical pack's checked `L=3455` estimate. Both modules compile
from current source with the focused helper. This verifies the sender adapter
that had been open in the preceding entry, but the D2 schedule's actual address
maps do not yet have a useful uniform `G` bound from this argument; the
all-stage profile recurrence and terminal criterion remain open. The `3455*G`
pointwise route is therefore a checked bridge, not yet a coefficient-300
route. The Boolean 832-band / 448 aggregate-profile route remains numerically
more promising because it can avoid paying one worst-case global gap per key.

2026-10-30 profile-to-schedule gap audit: the 448 recurrence in
`D2VariableTilePhysicalFlowTransfer.lean` already allows separate cuts in
every tile/column and arbitrary destination tags. `D2StaticWireSets.lean`
identifies an ordinary sender port's intersection with any static address
cell as the exact union of its ordered gap-run fragments; the 4096-grid lemmas
then make each aligned fragment either a whole physical cell or empty.
`D2VariableTilePhysicalFlowTransfer.lean` proves the needed port-boundary and
hole-endpoint grid conditions *assuming* the actual `d2FlowStageInvInputs`.
Thus the remaining local composition is not another error estimate: it is to
construct, for every actual sender, the per-column cuts and receiver-tag map
from these fragments, and prove that grouping the tagged physical outputs
reproduces the next scheduled tile/column profile. This depends on the
all-stage sender-input invariant, still open. Once that assembly is proved,
the existing 448 theorem gives the checked `parentError + 448*tiles` step;
the global inversion exponent and terminal exact-sort contract remain
separate unproved obligations.

2026-10-30 source-refresh verification: the prior focused checks relied on
some stale or absent local `.olean` files. Rebuilt the dependency chain from
current source, including `D2Slope25LiftArea`, `D2ColumnRebatchBridge`,
`D2RowMajorFlowCuts`, `D2ClippedFlowProfileTransfer`, the physical-profile
mass/pack modules, `D2PhysicalFlowProfileTransfer`, `D2CutAlignment`,
`D2StaticWireSets`, and `D2VariableTilePhysicalFlowTransfer`; each focused
check passed. In particular, current source proves the variable-tile,
variable-cut, arbitrary-tag recurrence `error' <= parentError + 448*tiles`
and the 512-per-output-tile preservation when tile count doubles. This
confirms the algebraic profile step rather than the missing implementation
map: no checked theorem yet constructs the actual tile/column/port tags from
the scheduled comparator network, and the all-stage rank-profile induction
and terminal sort proof remain open.

2026-10-30 Stage-15 tail helper: `D2Stage15InactiveTail.lean` source-checks a
general lemma that all recursive stage-input obligations rooted at level 8
or deeper are vacuous for the stage-15 candidate. This separates the deep
inactive suffix from the four active odd levels for a future Stage-15 input
assembly. A direct composition with the actual level-seven path was attempted
but exceeded a 4,000,000-heartbeat elaboration budget while reducing the
expanded recursive run; that incomplete draft was removed. No Stage-15
preservation theorem was established by this step.
Refactoring the composition to mirror the balanced-root theorem's `let`
bindings still exceeded the 2,000,000-heartbeat default, so this should be
revisited by moving the actual-stage composition into the existing high-budget
stage module or by proving a shared opaque path projection first.

Follow-up: `D2Stage15LevelSevenInputs.lean` now source-checks that composition.
It keeps the sender tree behind the same nested-path `let` expression as the
balanced-root theorem, uses the stage-15 inactive-tail lemma for every child,
and applies the generic bot-rise input constructor. A focused check passed
with the 20,000,000-heartbeat budget used by the balance module. This closes
the complete stage-15 input predicate at active level seven; the actual
inputs at levels one, three, and five and the full Stage-15 invariant are
still open.

2026-10-30 Stage-15 active sender-input contracts: source-checked the
level-five balance projection and full middle-role input contract in
`D2Stage15LevelFiveInputs.lean` and `D2Stage15LevelFiveContract.lean`, the
level-three middle-role input contract in `D2Stage15LevelThreeInputs.lean`,
and the level-one input contract in `D2Stage15LevelOneInputs.lean`. The
level-one proof handles the `d = 14` top-descending startup case separately
from later top-rise quota accounting. Together with the previously checked
level-seven bot-rise contract, these close the local input obligations at all
four active Stage-15 levels. The root-level inactive wrapper and application
of the generic invariant-preservation theorem are now checked in
`D2Stage15PreservesInv.lean`: Stage 14's checked output invariant is carried
through the actual Stage-15 run to its output. This closes one actual stage
transition only; no all-stage recurrence, terminal sorting proof, or
coefficient-300 theorem follows yet.

Follow-up: `D2Stage16Frontier.lean` now source-checks the Stage-16 active
frontier and roles. For depth 14 the active levels are 2,4,6 with level two
top-rising; for every depth at least 15 they are 0,2,4,6 with level zero
top-descending, levels two/four middle, and level six bottom-descending.
This is schedule classification only: actual Stage-16 sender input contracts
and invariant preservation remain unproved.

Follow-up: `D2Stage16LevelSixRootCap.lean` source-checks the actual-run
level-six root-cap gate `512 * deficit <= capacity` for every depth and every
level-six address. The proof uses the six-edge stage projection to the
Stage-15 level-five middle sender, its checked recursive input contract, the
current parent subtree invariant, and the exact capacity identity
`capacity(d,6,16) = 2 * capacity(d,5,15)`. This closes one quantitative field
of the Stage-16 level-six sender contract. Balance, quota/allocation and
endpoint reserves, the other Stage-16 active levels, and invariant preservation
are still open.

Follow-up: `D2Stage16LevelSixBalance.lean` also source-checks actual level-six
balance from the Stage-15 level-five middle cut, and proves the Stage-16
level-six bottom-descending quota cap (`256 * quota <= capacity`) and evenness
at every eligible depth. Combined with the root-cap module these establish
balance, deficit cap, quota cap, and parity for this one active sender band;
allocation and both endpoint reserves remain open, so the full recursive
Stage-16 input predicate is not yet proved.

Correction / follow-up: `D2Stage15LevelSevenRootFull.lean` now source-checks
that every actual Stage-15 level-seven sender output has full root deficit.
`D2Stage16LevelSixInputs.lean` assembles this with the previously checked
Stage-16 root-cap, balance, quota, and parity lemmas to prove the complete
recursive input predicate for every actual level-six sender, all eligible
depths, and all addresses. Its proof also discharges both endpoint reserves
and the fresh-allocation inequality from the full level-seven child roots.
`D2Stage16LevelFourInputs.lean` now also source-checks the complete level-four
input contract: its level-five descendants recurse through the inactive band
to the level-six contract, and the Stage-15 level-five quotas fund the fresh
allocation and both endpoint reserves. The active Stage-16 bands at levels
zero and two, and therefore Stage-16 invariant preservation, remain open.
These are local checked stage interfaces, not an all-stage induction or a
global sorting/depth bound.

2026-10-30 Stage-16 input progress: `D2Stage16LevelTwoInputs.lean` now
source-checks the complete recursive input contract for every actual level-two
sender at all eligible depths. Together with the previously checked
`D2Stage16LevelFourInputs.lean` and `D2Stage16LevelSixInputs.lean`, this closes
all active non-root bands (including the depth-14 startup top-rise case).
Focused source check passed for the new level-two module. Stage-16 level-zero
input assembly and invariant preservation are addressed in the later completion entry; the global
all-stage invariant, physical address realization, rank-profile recurrence,
terminal sorting criterion, and depth-to-coefficient proof remain open. These
local stage lemmas do not establish a coefficient-300 bound.

2026-10-30 Stage-16 completion: `D2Stage16RootInputs.lean` now source-checks
the actual level-zero contract and composes all four active bands into
`d2FlowCandidateStage16_preserves_inv`, carrying the invariant through the
actual Run-16-to-Run-17 transition for every eligible depth. This supersedes
the preceding note that level zero and preservation were open. The focused
source check passed. The next scheduled transition is Stage 17; this result
still leaves all later stages, physical address realization, the global
rank-profile recurrence, terminal sorting, and the coefficient accounting
unproved.

2026-10-30 Stage-17 schedule arithmetic: `D2Stage17Frontier.lean` now checks
alpha(17)=1, alpha(18)=2 for depths 14-15 and 0 thereafter, and the exact
bottom frontiers omega(17)=7 and omega(18)=8. The active bands are formally classified as 1,3,5,7; level 1 is top-descending at depths 14-15 and top-rising thereafter, levels 3 and 5 are middle, and level 7 is bottom-descending. Only Stage-17 sender-input contracts and preservation remain.
2026-10-30 Stage-17 level-seven input completion: `D2Stage17LevelSevenInputs.lean` now kernel-checks the full recursive input predicate at every actual level-seven sender. The proof composes Stage 16's checked level-six sender contract (root capacity and balance), schedule quota/parity, the Stage-15 full-root provider, and preservation of those level-eight roots through the inactive Stage-16 deeper bands. This advances beyond the previously checked Stage-17 frontier classification. Stage-17 levels 1, 3, and 5 and the Stage-17 invariant-preservation step are still open; later stages, physical address/rank transfer, terminal sorting, and coefficient accounting remain unproved. Focused `check_prefix_flux_lean.py` passed for this module.


2026-10-30 Stage-17 level-six recursive input wrapper: `D2Stage17LevelSixInputs.lean` kernel-checks that every actual level-six node is inactive and that all eight child contracts follow from the newly checked level-seven inputs. Focused source check passed. This is the child-interface needed by the active level-five middle senders; no new full active-band contract or global bound is claimed.


2026-10-30 Stage-17 middle-band contracts: `D2Stage17LevelFiveInputs.lean` kernel-checks every actual level-five middle sender, deriving its endpoint reserves from the preceding Stage-16 level-six bottom-descending quota. `D2Stage17LevelFourInputs.lean` packages the inactive level-four wrapper, and `D2Stage17LevelThreeInputs.lean` checks every actual level-three middle sender, including the Stage-16 startup top-rise parent at depth 14. `D2Stage17LevelTwoInputs.lean` packages the inactive level-two wrapper. Focused checks passed for each module. Stage-17 level one and the Stage-17 invariant-preservation composition remain open; no global bound follows from these finite-stage contracts.


2026-10-30 Stage-17 level-one root gate: `D2Stage17LevelOneRootZero.lean` now kernel-checks that every actual Stage-17 level-one sender enters with zero root deficit. For depths 15 and above this follows from the Stage-16 root top-descending child reset; depth 14 is handled through the Stage-14 reset and the inactive root bands at Stages 15 and 16. Focused check passed. This supplies the zero-root field for the remaining Stage-17 level-one top-descending/top-rising contract; quota allocation and endpoint reserves for the top-rise case remain open.


2026-10-30 Stage-17 startup level-one contract: `D2Stage17LevelOneStartupInputs.lean` kernel-checks the complete recursive input predicate at depths 14 and 15. The proof combines the Stage-17 level-two wrapper, Stage-16 invariant preservation, and the checked Stage-17 zero-root reset to satisfy the top-descending gate. The later-depth top-rising level-one contract and Stage-17 invariant preservation remain open; this is local stage progress only and does not establish the coefficient-300 bound.


2026-10-30 Stage-17 invariant transition completed: `D2Stage17LevelOneStartupInputs.lean` now kernel-checks the full level-one input contract at all eligible depths. The later top-rise case uses the exact Stage-16 level-two quota relation (128 times the prior quota is 15 times the Stage-17 capacity), and proves every level-two child root has received that quota. The checked Stage-16 invariant gives the level-one balance; the inactive Stage-17 root assembles all level-one contracts. `d2FlowCandidateStage17_preserves_inv` then carries the invariant through Run-17 to Run-18. Focused source check passed. The all-stage invariant beyond Stage 17, physical provider/rank transfer, terminal sorting, and the coefficient accounting remain open; no global bound of 300 is established.


2026-10-30 Stage-18 schedule bridge: `D2Stage18Frontier.lean` kernel-checks the full even-band active frontier (levels 2,4,6,8 at depths 14-15; levels 0,2,4,6,8 thereafter), its exact top-boundary growth, and bottom-boundary drop. This identifies the active roles: top-descending at the startup top or level zero, middle on interior even bands, and bottom-rising at level eight. Stage-18 sender contracts and invariant preservation are not yet proved.


2026-10-30 Stage-18 bottom boundary: `D2Stage18LevelEightInputs.lean` kernel-checks the actual level-eight `botRise` contract at every eligible depth. The proof projects the Stage-17 level-seven `botDesc` write to each level-eight child, obtaining balance directly from the ordinary cut's child-root replacement; levels below the bottom boundary are handled by a generic inactive-tail induction. `D2Stage18LevelSevenInputs.lean` packages these as the inactive level-seven wrapper. Focused checks passed for both modules. The active Stage-18 level-six and higher contracts, and the Stage-18 invariant transition, remain open.


2026-10-30 Stage-18 level-six completion: `D2Stage18LevelSixQuota.lean` proves the exact 15/128 reserve ratio between Stage-17 level-seven bottom-descending quotas and Stage-18 level-six capacity, and proves the actual level-seven child-root quota floor by projecting through Stage-17's inactive level six and active level-seven cut. `D2Stage18LevelSixInputs.lean` combines this with Stage-17 level-five balance/root-cap data to kernel-check the full recursive Stage-18 level-six middle-sender contract, including fresh allocation, parity, and both endpoint reserves. `D2Stage18LevelFiveInputs.lean` supplies the inactive wrapper. Focused checks passed for all three modules. The active Stage-18 levels 0, 2, and 4 and the invariant transition remain open.


2026-10-30 Stage-18 level-four band and moving top-band arithmetic: `D2Stage18LevelFourQuota.lean` and `D2Stage18LevelFourInputs.lean` kernel-check the full level-four middle-sender contract, using the Stage-17 level-three quota floor; `D2Stage18LevelThreeInputs.lean` supplies the inactive wrapper. `D2Stage18LevelTwoQuota.lean` kernel-checks that the Stage-18 level-two middle quota is exactly one sixteenth of the inherited Stage-16 level-two reserve and establishes the capacity/parity inequalities needed for a late-depth contract. Focused checks passed for all four modules. The level-two startup/late input contracts and invariant transition remain open; this is still local bridge work and does not establish a global bound.


2026-10-30 Stage-18 invariant transition completed: `D2Stage18LevelTwoQuota.lean`, `D2Stage18LevelThreeQuota.lean`, `D2Stage18LevelTwoLateInputs.lean`, `D2Stage18LevelTwoStartupInputs.lean`, and `D2Stage18LevelTwoInputs.lean` kernel-check the late middle and startup top-descending level-two contracts, including the actual child-root quota floor. `D2Stage18LevelOneInputs.lean` supplies the inactive wrapper; `D2Stage18RootInputs.lean` assembles the root contract and carries the zero root from Stage 16 through Stage 17. `D2Stage18PreservesInv.lean` kernel-checks Run 18 to Run 19 for every eligible depth. Focused source checks passed. This extends the finite stage prefix only: the arbitrary-stage reserve invariant, physical port/tag realization, terminal exact sort, and depth coefficient proof remain open.

2026-10-30 reusable sender-visit interfaces: `D2TwoStageEndpointReserve.lean` combines half-quota creation at an ordinary cut with monotonicity through the intervening inactive same-level stage, and packages the matching parent-exported child-cap/balance fields. `D2CandidateQuotaLower.lean` proves the integer schedule's quota floor and packages the two-visit reserve transition for every ordinary current sender whose two-stage predecessor is ordinary; the schedule already isolates the exceptional bottom-rise predecessor. `D2Stage18ReserveViaTwoStep.lean` instantiates the reserve interface on the actual Run-16-to-Run-18 level-four subtree from the checked Stage-16 input contract. All three focused Lean checks pass. These close two local ingredients, not the full arbitrary-stage induction: combining parent exports, ordinary predecessor reserves, allocation/quota gates, and the startup/top-descending and bottom-rise bases into all-stage sender inputs remains open.

2026-10-30 allocation gate reduction: `D2AllocationFromEndpointReserve.lean` proves that `quota <= allocation` follows from one endpoint reserve, `512*deficit <= cap`, and `256*quota <= cap`: the endpoint gives `cap <= 128*totalChildDeficit`, hence `4*deficit <= total` and `2*quota <= total`, so `deficit+quota <= total`. It defines a recursive sender-input contract omitting the allocation conjunct and proves that this reduced contract implies the existing contract and suffices for one-stage invariant preservation. Focused Lean check passed. This removes one arithmetic gate from the prospective all-stage induction but does not prove its other sender inputs or the global sorting bound.

2026-10-30 exceptional bottom-rise reserve base: `D2BotRiseReserveArithmetic.lean` kernel-checks the schedule identity that, two stages after a `botRise` boundary, the active sender capacity is exactly 128 times one native child size. It also proves the local tree transition: if the child endpoints are native and inactive during `botRise`, they retain the required reserve through the next inactive same-level stage. Focused Lean check passed. Connecting the native-history trace to the arbitrary-path candidate run remains part of the all-stage induction.

2026-10-30 two-step bottom-rise reserve interface: the integer schedule identity and a generic two-stage recursive-tree reserve lemma now cover the local `botRise` exceptional branch in `D2BotRiseReserveArithmetic.lean`. The module passes the focused Lean check. Its remaining premise is the native endpoint state at the actual arbitrary-depth sender path; the existing history/trace lemmas are the intended bridge. This is a local base-case interface, not the arbitrary-stage induction.

Follow-up to the bot-rise base: `d2FlowTreePathHistory_child_root_preserved` is now kernel-checked for arbitrary path depth. It states the exact trace condition needed to transport a native child root through the selected recursive-tree history; the remaining instantiation is to discharge that condition from the candidate schedule's bot-rise window for every path.

2026-10-30 botRise reserve trace bridge: D2BotRiseRunBridge.lean now kernel-checks the candidate schedule's exceptional two-stage bottom-rise window at every eligible depth. For any recursive path, the child-root deficit after the two callbacks equals its pre-window value: the child stays inactive throughout, while the parent is inactive except for the botRise callback, which also preserves that endpoint root. This packages the checked local reserve arithmetic into an actual-run trace lemma. It does not establish the arbitrary-stage sender invariant, physical port/tag realization, terminal exact sorting, or the coefficient-300 bound. Focused source check passed.
The same module also exports d2FlowCandidateRun_botRise_path_child_bound, the direct reserve-transport corollary for callers: any pre-window lower bound on that child root is retained after Run at stage 3*j+2.

2026-10-30 inversion stress extension: the (3,3,2) input-dependent sparse oracle at depth 200 was run on band and outer initial profiles. Both ended below the conditional N^(27/301) cleanup gate: 556,516 inversions (exponent 0.03114) and 2,499,100 (0.03467), respectively; each explored 6,099,968 compressed states and left 1,492 mixed wrong bits. This is finite oracle evidence only, not a fixed-provider bound. The all-input profile recurrence remains the central blocker.

2026-10-30 terminal audit of the 448 profile recurrence: its global l1 allowance parentError + 448*tiles permits errors spread over every tile, so it cannot alone imply a single localized dirty band or constant-count seam cleanup. The Boolean profile route still needs a multiscale/maximum-tile terminal contract (or priced distributed cleanup), in addition to the actual schedule tag map and all-stage sender invariant. This sharpens the terminal gap; it is not a counterexample to the fixed provider.

2026-10-30 receiver-tile incidence screen: added eceiver_fiber_types.py, which works over the shared FlowDAG state types rather than enumerating all wires. For (3,3,2), row scale 8192, it checks every reachable parent-state context at each stage and finds at most four distinct input physical tiles contributing to any one receiver physical tile through depth 9 (DAG nodes 301). A second, direct global-cell screen cross-checks the type calculation through depths 5-7; wire_partition_check.py --depths 5 6 --scales 8192 --params 3 3 2 --compressed still passes after adding an explicit per-node transition map to low_dag.py. The scripts track static 4096-cell ownership and tile incidence only; they do not prove the all-depth fan-in bound or a key-profile recurrence. eceiver_ancestor_screen.py further finds maximum full-schedule source-tile ancestry 9, 4, and 5 at depths 5, 6, and 7, respectively. This is encouraging finite evidence but is nonmonotone and does not yet bound asymptotic terminal error. The key next gate is a proof of the schedule-uniform cell-to-cell routing relation plus a closed spatial error potential; bounded one-step fan-in alone can still amplify per-tile errors.

2026-10-30 Exact cell routing bridge: `D2StaticWireSets.lean` now proves that any 4096-element fragment whose intersection with each aligned static 4096-cell is whole-or-empty must equal one such cell. `D2VariableTilePhysicalFlowTransfer.lean` composes this with the existing grid-aligned static-gap/rank-slice facts: every fitting 4096-rank fragment of a static-gap sender is exactly one physical cell. Focused checks passed for both modules. The result makes cell-level sender routing exact under the stated alignment hypotheses; it does not yet prove the all-depth spatial error recurrence, terminal sorting, or coefficient accounting. Next, instantiate it for the actual scheduled sender ports and determine whether cell ancestry admits a closed all-depth potential.

2026-10-30 Rank-port cell lift: `staticGapRankPort_cells` now divides any aligned sender rank port of length q·4096 into q aligned rank fragments and identifies a physical 4096-cell for each fragment. It composes the static-gap result with the existing grid-aligned port boundaries. The theorem currently gives per-fragment cell witnesses; pairwise distinctness and a packaged finite cell map are not part of the statement. More importantly, no closed spatial error potential or terminal purity bound has been proved, so the ≤300 objective remains open.

2026-10-30 Injective port-cell map: `staticGapRankPort_cells_injective` upgrades the per-fragment witnesses to an injective map from the q rank cells of any aligned port into distinct physical cells. Distinct rank fragments have disjoint `blockOf` sets, so they cannot share a physical cell. The existing port-grid bridge is conditional on all-stage sender-input contracts, and the universal provider for those contracts is still unproved. The remaining use of this map is to close a spatial key-error potential, which is also open.

2026-10-30 Stage-19 frontier: `D2Stage19Frontier.lean` kernel-checks alpha(19), alpha(20), omega(19)=7, omega(20)=8, and the actual active bands: levels 3,5,7 at depths 14-15; levels 1,3,5,7 from depth 16 onward. It classifies the top role as `topDesc` at depths 14 and 16 and `topRise` at depths 15 and 17+, with level 7 `botDesc` and interior active levels `mid`. Focused check passed. This is schedule classification only; Stage-19 sender inputs and the all-depth provider remain open.

2026-10-30 Run-18 native-tail preservation: `D2Stage18LevelEightChildrenFull.lean` kernel-checks that for every actual level-eight path, its level-nine child subtrees at Run 18 are exactly the corresponding full native subtrees from initialization. The proof uses the stage-history model: level eight is inactive in updates 0-17, and every deeper active predicate is false over that window. This isolates the next reserve step: Stage 18's level-eight `botRise` fills each level-eight root to the total mass of these eight native children, providing Stage 19's level-seven endpoint reserves. Stage-19 sender inputs and the all-depth provider remain open.

2026-10-30 Native bot-rise mass lemma: `D2NativeBotRise.lean` proves that a valid `botRise` whose eight child roots equal their native sizes fills the parent root to its native size. Together with the checked Run-18 level-eight child-preservation theorem, this isolates the mass identity needed for Stage-19 endpoint reserves. The remaining bridge is to identify the actual post-Stage-18 level-eight roots inside the Run-19 tree and package the Stage-19 level-seven sender inputs; no all-depth provider or sorting-depth theorem follows yet.

2026-10-30 Stage-19 invariant transition completed: `D2Stage19LevelSevenInputs.lean`, the new level-five/three/one floor and input modules, and `D2Stage19PreservesInv.lean` all pass focused Lean checks. The full Run-19-to-Run-20 reserve-invariant step is proved for depths d >= 16, including the depth-16 top-descending exception. This closes one finite transition only; arbitrary-stage induction, physical rank/port transfer, terminal sorting, and the coefficient bound remain open. See `D2-STAGE19-CLOSURE.md`.

2026-10-30 Stage-20 bottom gate: `D2Stage20LevelEightArithmetic.lean` and `D2Stage20LevelEightInputs.lean` pass focused source checks. The actual Run-20 level-eight `botDesc` senders inherit the regular-child root cap and balance from Stage 19 level seven; their eight level-nine children remain native and full, giving the mass and endpoint reserves, while levels beyond nine are inactive. This is only the bottom band: Stage-20 levels six, four, two, and the root contract are still needed before Run-20-to-Run-21 invariant preservation. The arbitrary-stage provider, physical rank/port realization, terminal sorting, and coefficient-300 accounting remain open.

2026-10-30 Stage-20 level-six contract: `D2Stage20LevelSixInputs.lean` passes a focused source check. Its cap and balance follow from the Stage-19 level-five regular cut; each level-seven child gains the Stage-19 `botDesc` quota, which exceeds the Stage-20 endpoint threshold by a factor of 15; and the level-seven wrapper uses the verified level-eight input theorem. The level-four, level-two, and root contracts are still required for Run-20-to-Run-21 preservation. No arbitrary-stage provider or coefficient-300 theorem follows from these finite gates.

2026-10-30 Stage-20 level-four contract: `D2Stage20LevelFourInputs.lean` passes a focused source check. It uses the Stage-19 level-three regular-child bound and balance, the level-five `mid` quota as a 15-fold endpoint floor, and the verified Stage-20 level-six contracts below it. Stage-20 levels two and zero remain before this finite transition can be composed; the arbitrary-stage provider, physical transfer, terminal sorter, and coefficient accounting remain open.

2026-10-30 Stage-20 invariant transition completed: the focused source checks pass for `D2Stage20LevelTwoInputs.lean`, `D2Stage20RootInputs.lean`, and `D2Stage20PreservesInv.lean`, in addition to the arithmetic and level-eight/six/four modules above. Run 20 to Run 21 now preserves the reserve invariant for every `d >= 16`; the depth-16 level-two top-descending and inactive-root cases are included. This supersedes the earlier notes that Stage-20 levels two and zero remained open. See `D2-STAGE20-CLOSURE.md`. This finite bridge does not prove arbitrary-stage coverage, physical rank/port realization, terminal sorting, or the coefficient-300 bound.

2026-10-31 depth-8 receiver-ancestry audit: the existing set-based screen completed at depth 8 (10 schedule transitions, 176 FlowDAG nodes, 524,288 terminal tiles) and reported unique source tile identifiers 1,3,5,7,9,9,9,9,9,9,9 across backward horizons. This is only a spatial-identifier diagnostic: it collapses a tile that reappears at different stages, so it does not bound accumulated fresh profile error. Use a stage-labelled cone before drawing a terminal-error conclusion; no all-depth ancestry or profile-potential theorem follows.

2026-10-31 stage-labelled ancestry and aggregate budget: the corrected exact screen completed at d=7 (7 transitions, 91 DAG nodes) and d=8 (10 transitions, 176 nodes). The maximum live tile footprint by backward horizon was [65,536,3,5,5,5,5,5,5] and [524,288,3,5,7,9,9,9,9,9,9], respectively; the maximum total tile-stage visits in one terminal cone was 34 and 79. These are finite diagnostics only; the cones grow across depth and still need an all-depth spatial bound.
`D2GeometricProfileBudget.lean` now kernel-checks the aggregate recurrence: if tile counts double, each stage adds at most 448 error units per input tile, and the initial error is at most 512 per initial tile, then at every stage total error is at most 448 per current tile plus 64 per initial tile. Focused `lake env lean` check passed. This sharpens the abstract aggregate budget, but does not bound terminal rank displacement or instantiate the actual schedule tags.

2026-10-31 geometric budget corollary: `D2GeometricProfileBudget.lean` also proves that after six doublings, the abstract aggregate profile error is at most 449 units per current tile (given the 512-per-initial-tile start and +448-per-input-tile stage transfer). The proof is kernel checked with `lake env lean`. This tighter scalar budget still does not control the signed cumulative error across ordered receiver tiles.

2026-10-31 boundary-only weighted-error interface: `D2WeightedPortDefect.lean` now proves `abs_weighted_prefix_increments_le_internal_variation`. When actual and ideal profiles have zero defect at both sender endpoints, weighted port error is charged only by internal variation of the port weights; constant weights cost zero. This is the algebraic step needed to charge local profile error only to sender ports cut by a global prefix. Focused source check passed. The remaining geometry is to construct the actual prefix-indicator weights and bound the number/variation of crossed sender ports over all levels.

2026-10-31 prefix-weight variation sharpening: `D2WeightedPortDefect.lean` now also proves that a nonincreasing {0,1}-valued port weight has internal total variation at most one. With zero endpoint defects, the fixed-core weighted profile error is therefore bounded by its 896 local endpoint allowance only when the prefix indicator changes across a port. This gives the exact boundary-only charge needed for a global-prefix recurrence; actual schedule prefix-indicator construction, sender-boundary count, and contraction of the initial defect remain open. Focused source check passed.

2026-10-31 native-interval boundary aggregation: `D2StaticWireSets.lean` now kernel-checks that disjoint native intervals have at most one interval crossing a fixed global prefix per level, and that a static-gap sender can cross a cut only when its parent interval crosses it. Consequently, if the local 896 port-error allowance is charged only on crossing senders, its aggregate contribution is at most `896 * levels` per stage. This is an additive recurrence interface, not yet an actual-schedule theorem: the active sender-to-native-parent map and zero-endpoint profile hypotheses still need to be established, as does a bounded initial prefix defect.

2026-10-31 native path geometry: `D2NativePathIntervals.lean` kernel-checks a base-eight index for every recursive flow path, injectivity at a fixed depth, and disjointness of the corresponding fixed native intervals. It combines this with static-gap containment to prove that at most one same-depth sender crosses any fixed prefix cut; summing the local 896 charges over all depths gives at most `896 * (depth + 1)` per stage under the explicit containment and local-error hypotheses. This closes the abstract same-level geometry/count, but the actual comparator trace has not yet been identified with these path-indexed static-gap senders. Nor does a pointwise prefix-defect budget alone localize all misplaced keys; a rank-displacement/moment potential and a bounded initial state are still required for terminal cleanup.
