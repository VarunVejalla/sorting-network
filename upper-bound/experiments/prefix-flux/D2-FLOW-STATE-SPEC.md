# Concrete state and transition for the D2 flow

2026-10-22. This is a specification of the executable recurrence in
`flow_dag.py`, not a proof that its proposed invariant holds and not a sorting
or asymptotic theorem. Its purpose is to give a precise target for a Lean
bridge from `D2ScheduleReserve.lean` to reachable flow states.

## State represented by one node

At level `i` and stage `t`, each node stores `(G,L,H)` and its ordered child
nodes. Its native size is `R_i = scale * 8^(d-i)`. `G` is its missing/deficit
mass; `L` and `H` are the portions of that deficit assigned to the low and
high ends. A non-leaf's allocation is

```text
A = sum_j G(child_j) - G,
```

and a leaf's allocation is `R_i-G`. Every state has `0<=G<=R_i` and
`L,H>=0`. For `G<R_i`, the endpoint invariant is `L+H=G`. For `G=R_i`,
the node is the saturated/empty sentinel: interval interpretation returns
empty and imposes no balance equation on `L,H`. The initial tree has
`(G,L,H)=(0,0,0)` at the root and `(R_i,0,0)` at every non-root node. Thus
only the root initially has positive allocation.

## One stage, exactly

To form stage `t+1` from stage `t`, recursively update every child first. An
inactive node keeps its own `(G,L,H)` and points to those updated children.
For an active node, compute `A` from the **old** parent and old child-root
deficits `U_j`; descendant recursion changes the child descendants, but does
not change the child roots used for this allocation and cut.

* `botRise`: set `pi=A`; leave all recursively updated child roots untouched.
* `topDesc`: set `pi=0`; overwrite every child root with `(0,0,0)`. The
  executable final conservation assertion forces `G=0` in this branch.
* Other roles: set `pi` to the scheduled quota, require it even, and require
  disjoint fronts
  `X=L+pi/2 <= Y=sum_j U_j-H-pi/2`. For child `j`, with old interval
  `[s_j,e_j)` in the concatenation of the `U`s, define
  `cl_j=|[s_j,e_j) intersect [0,X)|` and
  `ch_j=|[s_j,e_j) intersect [Y,sum U)|`. Its new root is
  `(cl_j+ch_j,cl_j,ch_j)`; its already-updated descendants remain in place.

The implementation checks nonnegative block sizes and exact conservation;
for ordinary cuts these imply `pi<=A`. For all active roles the new parent root is
`(G+pi, L+floor(pi/2), H+pi-floor(pi/2))`. The cuts partition the allocation:
for ordinary cuts, `sum_j (U_j-cl_j-ch_j)+pi=A`; for `botRise`, the block
sizes are zero and `pi=A`; for `topDesc`, the equality follows from `G=0`.
This recursive order and child overwrite are
essential: cuts use the old child-root sizes while the overwritten child keeps
its recursively updated descendants. The abstract two-stage identity applies
only after ordinary cuts are proved unsaturated at the two end children.

## Induction obligations for the proposed bound

For each stage, prove on the actual recursively reachable tree:

1. `0<=G<=R_i` and `L,H>=0`; at each non-leaf also prove
   `G<=sum_j G(child_j)`, so the allocation subtraction is exact and
   nonnegative. Additionally, `G<R_i` implies `L+H=G`, and every reachable
   active node satisfies the balance assertion required by `step`. This
   sentinel-aware invariant makes allocations nonnegative and bounded by
   native size.
2. At every ordinary positive-up sender, with `c=scale*cap(d,i,t)`, prove
   `G<=c/512`, `pi<=c/256`, and each current endpoint child deficit is at
   least `c/128`. These three facts imply each cut front lies inside its
   designated end child; front noncrossing alone does not imply this.
3. Prove the same bounds for the appropriate predecessor and intermediate
   child states. Only then may the ordinary two-stage conservation identity
   in `D2ScheduleReserve.lean` be instantiated to give `A/c<=279/256`.
4. Handle startup, `topDesc`, and `botRise` by their concrete branches above;
   for `botRise`, child-root preservation must be carried through the actual
   recursive state, not supplied as an independent trace hypothesis.

## Two-step endpoint-reserve induction target (2026-10-24)

The schedule and arithmetic lemmas already in `D2ScheduleReserve.lean` reduce
the endpoint-reserve obligation to one simultaneous induction over sender
visits. For an ordinary active sender `(i,t)`, use the endpoint reserves at
that sender to contain its two cut fronts. Then prove the reserves needed at
its next same-level visit as follows:

* Startup: at `(i,t)=(1,1)`, the level-two children are native and their
  deficits exceed `c/128`. At `(i,t)=(2,2)`, the level-three children are
  native and their deficit is exactly `c/128`.
* Strong descending base: if the same-level sender at `t-2` was `botRise`,
  `active_regular_prev_two_role_cases` and the schedule force the current
  visit to be `botDesc` at `t=3*i-4`. The children are still below the bottom
  active frontier, so their deficits are native; native child size is exactly
  `c/128` at this phase. The trace lemma
  `botRise_children_parent_trace_native` is the intended actual-state bridge.
* Ordinary predecessor: otherwise the sender at `t-2` has role `topRise`,
  `mid`, or `botDesc`. Its quota is at least `15*cOld/4096` (top-rise is
  larger). If its cut is contained in the endpoint child, that endpoint's new
  deficit is at least `piOld/2`. The same-level sender is inactive at `t-1`,
  so the endpoint deficit can only stay fixed or increase during that stage.
  Since `cOld=16*c`, this gives
  `G_endpoint >= 15*c/512 >= c/128` at the current visit. The abstract
  transport is `d2_scheduled_endpoint_reserve_persists`.

The schedule branch split was exhaustively checked at depth1000: among
373,250 ordinary active senders, exactly two are startup bases; every other
sender has an ordinary two-stage predecessor, except the strong `botRise ->
botDesc` base cases. Reproduce the finite schedule check with
`python upper-bound/experiments/prefix-flux/d2_schedule_parent_gate.py --depth 1000`.
The script is diagnostic; the corresponding all-depth schedule cases are
already represented by `active_regular_prev_two_role_cases` and the frontier
lemmas in Lean.

The matching actual-flow audit passes through depth100: 204,348 ordinary
sender states satisfy deficit, quota, and both `c/128` endpoint-reserve
conditions across the 744,031-node interned flow. Reproduce with
`python upper-bound/experiments/prefix-flux/d2_reachable_reserve_audit.py --depth 100 --scale 8192`.
This cross-checks the two-case induction against the exact finite recurrence;
it does not prove the simultaneous input invariant for arbitrary stages.

The missing theorem is the composition with the actual recursive tree: prove
that every predecessor cut is contained using its own inductive endpoint
reserves and sender cap, transport the reserves across the intervening stage,
and simultaneously obtain the current sender cap from its previous-stage
parent cut/reset. Then apply the existing two-step noncrossing/allocation
lemmas and `d2FlowStage_preserves_inv_of_tolerant_inputs`. This would replace
the stage-by-stage wrappers with one arbitrary-stage induction. It is not yet
formalized here; passing finite audits and the abstract schedule lemmas do not
close this composition. Even after it closes, the global rank-transfer and
sorting obligations remain.

`D2ScheduleReserve.lean` now defines `D2FlowTree`, its saturated-aware
`d2FlowTreeInv`, the full-subtree initialization, and a callback-parameterized
recursive `d2FlowStage`. Its candidate callbacks now encode the rounded D2
activity and role, plus integer quotas at scale8192. Kernel-checked lemmas
match activity and roles to the schedule and show that active-point integer
fixed quotas (top-rise, mid, and bottom-descending) equal the rational
`d2PortSize` formulas; bot-rise instead takes the live allocation directly.
The exponent bound is `c>=2^20`. The root has tree index `d`, hence native
size `scale*8^d`; its allocation at initialization is kernel-checked to equal
that full input size. Prefix-sum child positions are kernel-checked to be
contiguous. The cut lengths telescope across the eight child intervals, and a
kernel-checked `d2FlowOrdinaryCut_conserves` theorem proves that ordinary cuts
sum to `G+pi` under balanced parent endpoints, even `pi`, and in-range,
noncrossing fronts. `d2FlowStage_regular_child_mass` composes that identity
with the actual recursive-stage projection, proving the post-stage child-root
deficits sum to the updated parent deficit for active top-rise, mid, and
bottom-descending nodes under those same hypotheses. `topDesc` has the same
aggregate property under its required `G=0` guard. The tree-stage projection
lemmas identify ordinary child roots with the local cut formula, clear children
for `topDesc`, and retain recursively advanced child roots for `botRise`. These
are local branch bridges; one-stage invariant preservation is still open.
The leaf case preserves the leaf, and a schedule lemma proves leaves inactive
through the candidate horizon. The transition uses total natural subtraction;
correspondence with the asserting Python step still requires conservation,
even quotas, and valid cut fronts. The invariant now also requires each
non-leaf deficit to be covered by the sum of its child deficits, making the
allocation an exact subtraction. The strengthened initial-tree invariant is
kernel-checked. Exact `FlowDAG` scans at scale8192 found no reachable node
violating child-cover through depth100, including 373,240 reachable non-leaf
states at depth100; this is finite diagnostic evidence only. Lean proves every
recursive stage is root-deficit monotone and proves child-cover preservation
for inactive parents and `botRise`; ordinary roles preserve it as equality
under the cut hypotheses, and `topDesc` does so under `G=0`. Thus this clause has a local
branch-by-branch preservation proof. For `botRise`, Lean also proves the
updated parent remains within native size from child native bounds and
child-cover. For an ordinary active node, a further conditional theorem now
preserves the full tree invariant from recursive child invariants, balanced
parent endpoints, even/noncrossing in-range cuts, and explicit parent/child
native-cap bounds. The companion `d2FlowStage_regular_node_inv_of_reserves`
derives front fit and those caps from the established reserve theorem, assuming
quota is at most the actual allocation, sender deficit/port bounds, and
endpoint-child reserves. It uses the local overwrite fact that cuts remove no
more than the old child deficit. `d2FlowCandidateQuota_le_scaled_allocation`
converts the existing normalized port inequality into the exact scale8192
integer `quota<=allocation` statement, and
`d2FlowCandidateStage_regular_node_inv_of_reserves` composes that conversion
with the stage theorem. The candidate wrapper now takes its capacity to be the
exact integer candidate capacity and derives `256*quota<=capacity` from the
regular-role quota formulas, rather than assuming this cap separately. The
candidate exponent lower bound also proves the quota even, removing that
separate premise from the candidate node wrapper. A recursive allocation
lemma proves that the
invariant bounds each actual subtree allocation by its native size;
`d2FlowCandidateTreeAllocation_le_native` normalizes this at scale8192 to the
schedule's `nativeD2 d i`, supplying the native-allocation hypotheses in the
two-step role split directly from reachable trees. Lean proves that subtree
runs with arbitrary parent root overwrites project to another history of the
same form (`d2FlowTreeRun_child_as_history`), and the actual candidate
full-tree run, including the stage-zero bootstrap, is such a history
(`d2FlowCandidateRun_eq_generic_history`).
Consequently its immediate child deficit satisfies the exact
`d2ChildDeficitTrace` recurrence with the concrete candidate callbacks and
parent cuts (`d2FlowCandidateRun_child_trace`). These lemmas close the
history/trace adapter gap needed to iterate the analysis down a path; they do
not establish the numerical trace bounds. The
`d2FlowCandidateStage_actual_port_eq_schedule` theorem further identifies
every active subtree's normalized actual port with its scheduled
`d2PortSize`, including the allocation-based `botRise` case under child-cover.
The main open obligation is still to prove the sender deficit/quota bounds and
both endpoint reserves at every snapshot, so the two-stage identity and
endpoint-reserve induction can be instantiated globally.

## Stage-20 handoff (2026-10-30)

`D2Stage20PreservesInv.lean` now closes the finite Run-20-to-Run-21
transition (all actual bands, including the depth-16 startup split). Do not
continue extending this finite bridge stage by stage as a substitute for the
global argument. The next proof gate is the all-stage composition stated
above: use the actual child-trace adapter together with the ordinary two-step
sender-factor and endpoint-persistence lemmas to prove the tolerant sender
cap, allocation, and both endpoint reserves simultaneously for every actual
sender before termination. Only after that theorem passes should the proof
return to Lean stage preservation or the global sorting transfer. The
conditional 273 coefficient remains unproved.
`D2AllStageInvariant.lean` now packages the exact arbitrary-horizon closure:
if every actual Run-`t` tree satisfies the tolerant recursive sender-input
predicate for `t < n`, then Run-`n` satisfies the reserve invariant. Its
terminal-horizon corollary specializes `n` to `tfD2 d`. This is an induction
interface, not the missing provider: proving the tolerant inputs at every
actual snapshot, and proving that the terminal invariant yields a sorting
network with the claimed depth, remain open.
`D2TolerantSenderFactor.lean` sharpens the next arithmetic gate. With old
deficit ratio at most `23/4096`, the `279/256` sender factor follows for
regular child roles from their `15/4096` quota bound. In the exceptional
`botRise` child case it needs the pointwise profile `49/16384` on both endpoint
children and `1/256` on the six interior children; these sum to `241/256`
after the `32x` rescaling. The missing trace argument must produce that
endpoint profile from actual reachable parent/child states. Native-size caps
alone give only the coarser exceptional sum `1`, which does not close the
relaxed factor lemma.
`D2StrongParentRelaxedProfile.lean` proves the required cut geometry under
the tolerant `4096*G ≤ 23*cOld` cap: with equal native child deficits and the
strong-phase quota, both fronts fit inside their endpoint children, the six
interior deficits stay zero, and endpoint residuals have the exact `49/8192`
profile. After normalization, its port-profile corollary yields the sharp
`49/16384, 1/256, ..., 1/256, 49/16384` bounds, and the exceptional two-step
sender factor follows. This closes the local algebra/geometry gate. To use it
globally, the actual-run proof still must show the strong sender has those
equal native child deficits and that its children retain full native
grandchildren through the intervening `botRise` port visit.
`D2PathNativePreservation.lean` now proves the needed pre-strong-visit fact
on every actual candidate path: at level `i` and time `3*i-4`, all eight
child roots and all 64 grandchild roots still have their native values. The
child case uses the actual parent `botRise` callback window; the grandchild
case uses the schedule's inactivity window. Both are kernel checked, not
finite flow audits. This closes the native-state part of the local bridge.
`d2FlowStage_strong_cut_botRise_child_port` in
`D2StrongParentRelaxedProfile.lean` now proves that local composition: after
the strong cut, if child/grandchild roots are native and the schedule makes
those levels inactive, the next `botRise` port equals the child capacity left
after the updated deficit. The theorem is kernel checked. The remaining bridge
is to instantiate its quota/front-fit arithmetic on every actual candidate-run
strong sender, then feed the resulting child port profile into the coupled
all-stage input invariant. Neither that universal instantiation nor the global
sorting/depth conclusion is proved.
The local cases now compose through height induction in
`d2FlowStage_preserves_inv_of_inputs`; its recursive premise packages the
exact local conditions required at each sender. The actual bootstrap is
included and verified by `d2FlowCandidateBootstrap_preserves_inv`. The first
ordinary sender's local premise is verified in
`d2FlowCandidateBootstrap_sender_inputs`, which gives the full recursive
stage-one premise in `d2FlowCandidateStage1_inputs`;
`d2FlowCandidateStage1_preserves_inv` therefore proves the full tree
invariant through stage one for every `d >= 7`. The stage-two premise and
invariant preservation have since also been proved. The source modules
`D2ScheduleReserve.lean` and `D2Stage14PreservesInv.lean` extend this finite
prefix through stage 14: the latter proves
`d2FlowCandidateStage14_preserves_inv` for every `childDepth >= 7`, using the
level-specific contracts in the neighboring `D2Stage14*.lean` modules. Its
cached artifact is newer than its source, and a focused import check confirms
the theorem is available. This remains a finite stage prefix; proving the
sender premises uniformly for arbitrary stage index is still the central open
obligation.
The finite script `d2_reachable_reserve_audit.py` now checks the proposed
sender deficit/quota caps and both endpoint reserves on the actual `(3,3,2)`
FlowDAG through depth120: 357,195 active ordinary sender states passed, among
1,296,268 interned states. The executable step also checks allocation
conservation at each transition. These are finite diagnostics only; the hard
unproved part remains closing endpoint reserve and sender bounds together
over all stages.

## Concrete correspondence check

The executable definitions are `FlowDAG.initial`, `allocation`, and
`step` in `flow_dag.py`. Its `make` operation interns structurally equal
states, which changes representation but not the recursive transition above.
`subtree_interval` returns empty immediately when `G=R_i`, without inspecting
`L,H`. A finite audit at depth100 and scale8192 found 100 full/saturated
states with `L+H!=G`, versus no imbalance among 482,411 non-full states or
any active row. This is diagnostic evidence for the sentinel-aware invariant,
not its all-depth proof.
`D2ScheduleReserve.lean` proves schedule arithmetic, abstract local/trace
interfaces, the finite-tree transition, and the callback/history adapter
described above. It still lacks the reachable-state and global sorting proofs.

## Stage-two sender gate (2026-10-22)

Lean now proves the first sender's exact child-root profile in
`d2FlowCandidateStage1_child_profile`: for each level-one sender, only its
first and last children acquire deficit, each `2^(3d+7)`; the other six stay
at zero. Conditional on a stage-two level-two node having either endpoint
profile and full level-three children, `d2FlowCandidateStage2_sender_inputs`
proves all local obligations in `d2FlowStageInvInputs`. Here the role is
`botDesc`, the cap is `2^(3d+17)`, the quota is `15*2^(3d+5)`, and the native
level-three child size is `2^(3d+10)`, giving the exact tight reserve equality
`cap = 128 * childSize`. It also covers the zero-deficit interior nodes.

The stage-one child-tree shape is now connected to those local cases, and the
recursive premise composes across each first-sender subtree and the root
cleanup. `d2FlowCandidateStage2_inputs` proves the actual whole-tree stage-two
premise; `d2FlowCandidateStage2_preserves_inv` therefore establishes the
saturated-aware invariant through that complete stage for all `d >= 5` (input
dimension `d+2 >= 7`). Every later sender stage, the all-depth invariant,
provider/rank transfer, and terminal sorting theorem remain open.

## Stage-three frontier (2026-10-22)

Lean now classifies stage three's active roles: level one is `topRise`, level
three is `botRise`, and every level at least four is inactive. The recursive
input predicate for arbitrary stage-three subtrees below level four is proved,
as is the local `botRise` predicate from balanced root endpoints. The
stage-two cut profile is now formalized for equal full children with separate
left and right front widths; it gives the exact first/last child deficits and
zero interior deficits when both fronts fit in their endpoint children.
The first-stage endpoint deficits plus the stage-two half-quota are proved to
fit those full children. The stage-three level-one `topRise` input predicate is
also proved from a modular interface: recursive child premises, total child
deficit equal to capacity, and the two endpoint reserves suffice. A new Lean
bridge composes the stage-one endpoint profile
with the stage-two bottom-descending senders: it proves the predicted `38M`
endpoint deficits and `30M` interior deficits at level two. Using the actual
asymmetric cut profile, it also proves the stage-three recursive input gate at
level two, including the balanced root endpoints required by every level-three
`botRise`. It proves that the eight level-two child deficits in each first-sender
subtree sum exactly to `256M`, with endpoint reserves `38M` against a required
`2M`, and lifts these premises through the stage-two root cleanup. The concrete
whole-tree stage-three input theorem and saturated-aware tree invariant through
stage three are now kernel checked for every `d >= 5`.

For interpreting that profile, set `M=2^(3d+4)` where the tree dimension is
`d+2`. A stage-two bottom-descending sender has quota `30M`; its input endpoint
deficit is either `8M` or zero, so its low/high front widths are `23M` and
`15M` in some order (or `15M` each for an interior sender). Each front is at
most the full level-three child size `64M`. The resulting level-two deficits
are predicted to be `38M` at the outer endpoints and `30M` in the six interior
positions. Their sum is `256M`, exactly the stage-three level-one capacity;
the endpoint reserve requirement is only `2M`. The finite stage-three FlowDAG
snapshot agrees, but it is diagnostic evidence only. Stages after the third,
provider/rank transfer, and terminal sorting remain open; no end-to-end
coefficient below 300 has been established.

## Stage-four local gate (2026-10-22)

The stage-four frontier is kernel checked: level zero is `topDesc`, level two
is `botDesc`, and levels at least three are inactive. The local level-two
`botDesc` input theorem `d2FlowCandidateStage4_botDesc_inputs` now compiles
under the following actual-profile contract. With `M=2^(3d+4)`, the parent
level-two deficit must satisfy `G<=M/2`; its eight level-three children must
each have deficit `64M`. Then the level-two capacity is `512M`, the quota is
`15M/8`, and both endpoint reserve inequalities hold (the required capacity
is `4M`, against `64M` available at each endpoint). The quota is even and fits
within the remaining child mass.
The actual stage-three top-rise profile proves the parent bound `G<=M/2`.

The saturation arithmetic is now separately kernel checked in
`d2FlowCandidateStage3_botRise_saturates_native_children`: a stage-three
level-three `botRise` fills its root to `8192*8^(h+1)` when its eight
level-four children each retain `8192*8^h`. An inactive-node lemma also proves
that such a recursive call preserves the deficit at that node's root exactly.
The stage-two boundary bridge is also kernel checked:
`d2FlowCandidateStage2_boundary_grandchild_native` proves that its cuts leave
all level-four roots at native deficit, and
`d2FlowCandidateStage3_boundary_child_saturates` combines those reserves with
the bot-rise identity to prove each exposed level-three sender reaches `64M`,
assuming the stage-two cut fronts are disjoint. The first-stage endpoint
profile discharges disjointness for each actual stage-two boundary sender in
`d2FlowCandidateStage3_actual_boundary_child_saturates`. The new theorem
`d2FlowCandidateStage4_firstSenderSubtree_child_inputs` then composes those
native level-three roots with the stage-three top-rise endpoint profile and
proves the complete stage-four `botDesc` input gate for every level-two node
inside an actual first-sender subtree. These additions pass the focused check
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` from
`upper-bound/experiments/runaware`.

The wrapper `d2FlowCandidateStage4_inputs` now lifts the eight local gates
through the actual stage-three whole-tree snapshot and verifies the root
top-descending case. Thus the complete fourth-stage `d2FlowStageInvInputs`
predicate is kernel checked for every candidate dimension at least seven.
`d2FlowCandidateStage4_preserves_inv` then applies the global invariant
preservation interface and establishes the saturated-aware tree invariant
through all four scheduled stages for the same dimensions.

Stage five's schedule frontiers are now kernel checked for dimensions at least
nine: level one is `topRise`, and level three is `botDesc`. The local level-one
gate `d2FlowCandidateStage5_topRise_inputs` is also kernel checked under its
explicit profile hypotheses: the parent deficit is zero, each of its eight
level-two children has deficit at least `15 * 2^(3d-5)`, and each child's
recursive stage-five input predicate holds. Those numerical hypotheses match
the stage-four level-two `botDesc` quota scale. The theorem
`d2FlowCandidateStage4_levelTwo_reserves` proves that lower bound for every
level-two root in the actual output of stage four, for every input tree of the
candidate height. `d2FlowCandidateStage4_levelOne_roots_zero` verifies the
matching zero root profile, so the level-one top-rise gates are now connected
to the actual preceding stage. The wrapper
`d2FlowCandidateStage5_inputs_of_levelThree_inputs` proves the complete
stage-five input predicate assuming only the recursive input predicates rooted
at level-two nodes, where the level-three bottom-descending senders occur.
The new local theorem `d2FlowCandidateStage5_botDesc_inputs` closes each such
level-three predicate when its deficit satisfies the inherited `1/512`
capacity bound, its endpoint profile is balanced, and its level-four children
retain native deficits. All deeper stage-five calls are inactive.

## Stage-five actual bridge (2026-10-23)

The former bridge is closed. `d2FlowCandidateStage4_local_levelThree_cap`
exports the factor-two child cap from the actual stage-four level-two gate;
the capacity identity converts it to the stage-five level-three cap.
`d2FlowCandidateStage2_firstSenderSubtree_levelFour_native` proves the
native level-four reserve in the concrete stage-two boundary subtree.
`d2FlowCandidateStage4_levelTwo_source_levelFour_native` projects that
reserve through stage three's inactive level two and bot-rise at level three.
The generic `d2FlowStage_regular_child_grandchild_deficit` then transports it
through stage four, whose levels three and four are inactive. These facts give
`d2FlowCandidateStage5_actual_levelThree_inputs`; strict sub-native capacity
plus the tree invariant supplies the required endpoint balance.

`d2FlowCandidateStage5_actual_inputs` lifts the local gates to the complete
stage-five input predicate on the actual stage-four whole-tree output.
`d2FlowCandidateStage5_preserves_inv` consequently proves the saturated-aware
tree invariant through five scheduled stages for every dimension at least
nine. The focused check `lake env lean ../prefix-flux/D2ScheduleReserve.lean`
passes from `upper-bound/experiments/runaware`, with no `sorry` or `admit` in
the file.

The 279/256 aggregate factor, provider/rank transfer, and sorting terminal
theorem also remain open, so this does not yet establish a global coefficient
below 300.

## Stage-six bridge (2026-10-23)

The first repeating-schedule frontier classification is kernel checked by
`d2FlowCandidateStage6_frontiers`: the active roles are root `topDesc`, level
two `mid`, and level four `botRise`, with level six inactive. The exact
stage-five/stage-six capacity ratios are checked by
`d2FlowCandidateStage6_capacity_identities`. The local mid gate is checked by
`d2FlowCandidateStage6_mid_inputs_of_state`, assuming its actual-state inputs:
the level-two parent balance and `G<=c/512`, each level-three child receiving
at least the preceding stage's bottom-descending quota, and the recursive
stage-six input predicates below those children. `d2FlowCandidateStage6_actual_mid_state`
derives the cap and reserves from the actual stage-five top-rise and
bottom-descending outputs. The ordinary-cut root identity balances each
level-four bot-rise node, and the inactive tail, root cleanup, and level-one
recursion are packaged by `d2FlowCandidateStage6_actual_inputs`. Consequently,
`d2FlowCandidateStage6_preserves_inv` proves the saturated-aware invariant
through six scheduled stages for every `d>=9`. The all-depth invariant,
`279/256` sender bound, provider/rank recurrence, and sorting theorem remain
open; this finite extension does not make coefficient273 unconditional.

## Stage-seven and stage-eight frontier bridge (2026-10-23)

The second repeating transition is now closed. The stage-six level-four
endpoint reserves project through the actual whole-tree snapshot in
`d2FlowCandidateStage6_endpoint_reserves`. For the next stage, the local
bottom-descending gate was sharpened to require only its two endpoint reserves
and sufficient aggregate child mass, rather than a uniform reserve on every
child. `d2FlowCandidateStage7_actual_levelThree_inputs` proves those gates on
the actual stage-six output; the inactive level-two/root recursion and the
level-one top-rise gate are assembled by
`d2FlowCandidateStage7_actual_inputs`. Therefore
`d2FlowCandidateStage7_preserves_inv` carries the invariant through run stage
8 for every `d>=9`.

`d2FlowCandidateStage8_frontiers` is also kernel checked for `d>=10`: root
`topDesc`, level-two `mid`, and level-four `botDesc`. The stage-eight local
sender and endpoint gates are not yet proved. In particular, the needed
level-five endpoint reserves must be transported through the actual stage-seven
bottom-descending cuts. All-stage recurrence, the global `279/256` sender
factor, provider/rank transfer, and sorting terminal theorem remain open; the
conditional coefficient273 is not yet a theorem.

## Ordinary endpoint-reserve step (2026-10-26)

`d2FlowStage_regular_endpoint_quota_persists` formalizes one reusable induction
step. For a tolerant ordinary sender cut, if the old endpoint reserve is 16
times the next-stage capacity and the sender quota is at least `15/4096` of
the old reserve, both endpoint reserves survive the subsequent recursive
child update. The proof uses the exact endpoint profile from
`d2FlowStage_regular_child_profile_tolerant` and monotonicity of root deficit
under that child update.

The declaration and all preceding dependencies have since passed a complete
focused Lean check of the 18k-line file (2026-10-26). The step still assumes the actual cut's balance,
quota, and endpoint-reserve hypotheses; proving those uniformly from the
candidate schedule and reachable-state invariant, including startup and
exceptional roles, remains open. It is not an all-stage induction or a global
sorting bound.

## Minimal rank-state extension for the fixed-core provider (2026-10-26)

The existing `D2FlowTree` stores only `(G,L,H)` and child deficit counts; it
cannot supply the `tileMass`/`idealTileMass` premise of
`tiled_global_rank_error_le_parent_add_448_per_tile`. Keep that flow state,
but attach to each active sender an ordered tile-mass profile and its ideal
rank profile. Let `E` be the sum of their count-distances over tiles. The
checked fixed-core lemma gives the local transition

```text
E_out <= E_in + 448 * tiles.
```

If `E_in <= 512 * tiles`, then `E_out <= 960 * tiles`. The D2 child capacity
is `2 * 262144 * tiles`, so the normalized output error is at most
`15/8192 < 1/512`; this is enough to reinitialize the same sender cap at the
next scale. The missing formal step is a dependent profile on the actual
flow-tree transition: prove that port counts partition into the next active
senders' tile profiles and charge each incoming profile exactly once. The
current tree invariant proves only deficit conservation, not this rank-profile
correspondence. Even after that induction, a separate distance-weighted
potential is needed to get the sublinear inversion bound required by the
27-depth terminal-cleanup budget; aggregate `E=O(N)` alone does not imply it.

The finite aggregation part is now kernel-checked in
`D2RankRebatch.lean`: for any finite refinement of cells and any regrouping
map into output tiles, the total l1 count error after regrouping is no greater
than the sum of the cellwise errors. This covers the arithmetic once a split
at partial-tile offsets is specified. The remaining work is the actual
network-dependent map: define the refined cells from the D2 flow boundaries,
prove they partition each tile's ports, and show that regrouping them gives
the next active senders' 64-column profiles.

`wire_partition_check.py --compressed` now checks the exact static-address
routing identity modulo translation of a bag's base index. A context is its
shared FlowDAG state plus child slot; this is exact because interval endpoints
translate by the native bag width and rank slicing commutes with translation.
The compressed audit agrees with the exhaustive checker through depth 4, and
passes `(3,3,2)`, sparse-bottom, scale8192 through depth20 (32,750 distinct
state/slot routing cases at depth20). A selected-depth run at depth64 for the
target `(2,3,2)` sparse-bottom schedule also passes: 148 stages, 392,420
routing cases, and 125,101 shared states. The checker now accepts `--depths`
so a high-depth audit does not need to rebuild every smaller instance. These
remain finite geometry checks; they carry no key counts, separator execution,
or all-depth rank invariant.

`D2Slope25RebatchBridge.lean` composes this with the checked 448-per-tile
fixed-core contract. Given any explicit map from refined `(source tile, port)`
cells to output groups, it proves the grouped profile error is at most
`parentError + 448 * sourceTiles`. The group type can be
`Fin nextTiles × Fin 64`, so the conclusion can bound the complete 64-column
height profile, not just tile totals. When `nextTiles = 2 * sourceTiles` and
the parent error is at most `512` per source tile,
`rebinned_tiled_rank_error_preserves_doubled_budget` proves the grouped l1
error is at most `15/8192` of output capacity, below the `1/512` allowance.
The grouping map, refined cells, and their equality with the actual D2
next-stage 64-column profiles remain to be derived from the network; this is
not yet an all-depth rank invariant.

## Exact fixed-core transition needed for the global gate

The next state must retain each physical tile's 64 column heights, not only
its total `H`. For a Boolean threshold, write the input tile profile as
`h[c]` (`0 <= h[c] <= m`), and let `X[c,r] = [r < h[c]]`. The fixed first
shuffle/sort maps it to

```text
v[d] = sum_{c,r<m : (c + 35*r) mod 64 = d} X[c,r].
```

After the slope-25 shuffle/sort, the output profile is

```text
w[e] = sum_{d,r<m : (35*d + 25*r) mod 64 = e} [r < v[d]].
```

These are deterministic maps. Their arbitrary-height arithmetic is already
formalized by `slope35PhysicalOutputHeight` and
`slope25PhysicalOutputHeight` in `D2RankAlignment.lean` and
`D2Slope25Physical.lean`. In row-major layout, the sorted output's local
prefix count at wire cut `64*u+s` is exactly
`sum_{e=0}^{63} min(w[e],u) + sum_{e<s} [w[e]>u]` for `0 <= s < 64`. A
concrete global gate should link tile input heights to
the incoming ranked wire profile, impose this exact output map, and then split
the output prefixes at the D2 port boundaries into the children. This is the
correlation missing from `D2FlowTree` and from the selected-cut sender
polytope; replacing it by the checked 448 l1 estimate cannot exclude the
positive-drift witnesses already found there.

The modeling subgate is to encode this map first at a reduced row height using
unary Boolean variables for `X` and `[r < v[d]]`, compare its reachable
port-profile set against the current relaxation, and only then compress by
the 64-residue/quotient identities used in the local provider. A valid
all-depth state must also preserve partial-tile offsets when a D2 boundary
cuts a tile. No global exact-core recurrence or new coefficient follows from
the formulas alone.

For the limsup proof, it is enough to establish the construction on `N=8^d`
wires. The focused Lean module `D2PowerPadding.lean` proves both that
`minimum m <= minimum n` whenever `m <= n` (by restricting the larger
network), and that the fixed core width `4096*64=8^6` divides `8^d` for
`d>=6`. Thus every global core tile is complete on the cofinal power-of-eight
subsequence, and the general sizes follow by restriction with no asymptotic
loss. The same module proves that any affine bound on `minimum (8^d)` transfers
to the pointwise bound `minimum n <= A * Nat.clog 8 n + B` for all sufficiently
large `n`. This removes the final-tile padding obligation from the limsup
route; it does not address the internal D2 sender-to-tile ownership map.

## Reduced exact-core LP gate (2026-10-26)

The row-height-one case has a compact exact form: both column sorts are
identities, the first shuffle sends input column `c` to `d=c`, and the second
sends it to output column `e=35*c mod 64`. The exact encoding therefore uses
one Boolean input variable per wire in the tile, tied to the incoming prefix
profile, then imposes this permutation on every represented output prefix.
The index map was checked for all 64 positions. `--continuous-slope-core`
relaxes those Boolean occupancies to `[0,1]`; it is an outer relaxation, not an
exact Boolean network model.

There are two useful small gates, neither of which closes the target
recurrence. With `(x,y,z)=(1,1,1)`, `scale=64`, `row_count=1`, and depth 2,
the exact Boolean model solves optimally with 8 tiles and 1,827 variables.
Its `max_total_wrong` objective is 149, the same as the matched LP without the
core constraints. With the same parameters and `row_count=2`, the continuous
core LP also solves optimally at 84.5, unchanged from its matched baseline.
An earlier, uncompressed Boolean row-height-two MILP reached an incumbent of
74 with a dual-bound upper value of84 after60 seconds, against baseline84.5;
its gap was1.0, so this was not an optimality result. The source now uses a
smaller exact OR/AND encoding for height two. The corresponding toy MILP
(`(1,1,1)`, depth2, scale64) had no primal or dual bound after120 seconds.
The compressed model has 1,024 binary variables across four tiles, down from
1,536 in the unary encoding.
The OR/AND formulas were independently compared against the full height-two
shuffle/sort map on1,000 random column-height profiles.

For the target `(x,y,z)=(2,3,2)` schedule at `scale=64`, the exact Boolean
row-height-one model uses 32 tiles and 2,048 binary wire variables but did not
return a primal solution in the recorded run. The earlier row-height-one
results without Boolean wire variables were only continuous relaxations and
must not be read as exact-network findings. These tests show that local
two-shuffle constraints alone have little effect on the reduced objectives;
they do not identify the maximizing profiles as traces of the full sorting
network or establish an all-depth recurrence.

On the target `(2,3,2)` schedule with row height2, the continuous-core LP
improves the depth2 objective from554 to532.75, and the final global-prefix
defect from298.5 to290.2734375. At depth3, the objective is2218 both with and
without the core constraints; the core LP is optimal and has 53,337 variables.
For inversion area `M_1`, imposing source floor100,000 and optimizing
`M_1(out)-0.99*M_1(in)` gives `+1,618.01125` with the core and `+1,671.32`
without it; each optimizer preserves its source area exactly. So this simple
global moment does not contract at the tested rate, despite the shallow
terminal-objective improvement. The depth3 core inversion-drift model did not
return a primal point within120 seconds.

In the depth2 core-constrained `M_1` optimizer, all1,025 represented global
prefix defects are unchanged from stage0 to stage2 to within `3.5e-13`;
503 values are fractional. Thus the continuous core relaxation has a
stationary fractional profile, explaining why any potential depending only
on that profile cannot strictly contract in this gate. It is saved in the
ignored `LLM-helpers/sub300-core-inversion-profile.json`. Cross-column or
cross-stage Boolean correlations are needed to rule out this pseudo-state.

Reproduce the solved small row-height-one gate with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 2 --scale 64 --threshold 1/3 --params 1 1 1 --row-bits 0 --ordered-prefix --root-tail --all-global-cuts --exact-slope-core --time-limit 60
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 2 --scale 64 --threshold 1/3 --params 1 1 1 --row-bits 1 --ordered-prefix --root-tail --all-global-cuts --continuous-slope-core --time-limit 30
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 2 --scale 64 --threshold 1/3 --params 1 1 1 --row-bits 1 --ordered-prefix --root-tail --all-global-cuts --exact-slope-core --time-limit 60
```
