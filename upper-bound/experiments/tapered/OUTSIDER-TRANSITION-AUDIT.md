# Candidate outsider transition audit

Status: source-based obligations plus a Lean ordinary-kernel interface, October 12. This is not a global outsider theorem or a sorting bound.

## Ordinary interface

`TaperedOrdinaryKernel.lean` defines the candidate all-order predicate and a one-stage kernel modeled on `Chvatal.StageKernel`. Its theorem `tapered_outsider_step_of_kernel` shows that the kernel fields plus P(t) imply P(t+1) for ordinary levels. The kernel isolates these assumptions:

- a `PlacementStep` register-cover split;
- the capacity identity from the old parent reference capacity to the next child capacity;
- an order-zero parent-send bound, charging parent outsiders, sibling spill, separator B2 error, signed-window reserve, and active rounding;
- a higher-order parent fringe transfer with coefficient `1/86,000,000`;
- order-zero and higher-order child-up spill bounds;
- a separate level-zero case.

This is a proof interface, not yet instantiated by the actual recursive execution.

## Scalar checks with current constants

Use the definitions in `SignedReserve.lean`: `mu=17/71565312`, `delta=1/2^25`, `epsB=1/2^21`, and `reserve` as the endpoint reserve. If `c=C(parent,t)`, then `C(child,t+1)=4c`. The ordinary order-zero budget closes from the existing exact positive `screenedMargin`, assuming the parent-send field has the stated charge and the child-send field is bounded by `mu*delta*64^3*c`.

For higher order, the 64 child up-sends are bounded by `64^3*mu*delta^(r+1)*c` under P(t). Relative to the target `4*mu*delta^r*c`, the normalized child term is `64^3*delta^2/(4*delta)`; together with the fringe term `1/86,000,000`, `TaperedOrdinaryKernel.lean` proves the needed rational scalar inequality. The earlier risk note used obsolete constants; it has been corrected. At a complete sibling-prefix cut the separate aggregate spill term is about `1.19e-7` of parent capacity. This is already explicitly charged by `siblingFactor` in the candidate's screen; comparing it alone with the final residual margin was invalid.

## Which fields existing work supplies

| Field | Current status |
|---|---|
| Register coverage | `RaggedTreeRoute.raggedTreePlacementStep` now constructs an actual `PlacementStep` from a global `RaggedWirePartition`, conserved local splits, the canonical tree destination, and an injective wire-to-key map. Parent ports are the explicit `fromParent`; the exact routed remainder is `fromChildren`. For interior nodes, `routeRaggedWires_eq_parent_and_child_up` identifies that remainder with the 64 child up-ports. At terminal nodes the current total destination retains local down-ports, so those are part of the residual. This is ownership/coverage only; it does not prove numerical flow sizes or separator estimates. |
| Order-zero parent send | `VariableWindow` and `StageOneWindowGate` prove local rank-window/count statements; `TruncatedPaddedProvider` gives a padded local pack and conditional fringe transfer. There is no theorem applying these at every ordinary node and deriving the kernel's exact parent-send charge. |
| Higher-order parent fringe | The padded F2 provider gives a conditional high-side estimate. Its low-side live-prefix transfer and installation into the all-stage candidate routing remain open. |
| Child-up bounds | `tapered_child_send_bound_of_owned_cover` derives these bounds from P when the selected child-up sets cover `fromChildren`, belong to the matching child registers, and have the stated 4096 capacity ratio. `TaperedOrdinaryKernel` still presents the resulting bounds as fields; the real schedule has not supplied those cover/ownership/capacity premises. |
| Level zero | The root/bootstrap is a distinct transition and must provide its own all-order bound. The ordinary theorem does not discharge it. |

## Frontier cases remain separate

Top advance, top retreat, bottom expansion, bottom contraction, and the meeting/narrow-band cases recur. `FrontierDebtFlow` proves real mass identities, not key-set coverage or rank estimates. They need separate kernels; do not satisfy ordinary fields with artificial empty sender sets.

## Parent-send / fringe risk audit (October 12)

The local order-zero composition has no new combinatorial obstacle: `variable_window_wrong_le_signed_path` already turns two cumulative native-tail estimates into a wrong-rank count for an address-dependent slot, with the candidate reserve. `separator_output_wrong_keys_le` then turns that count plus both output-boundary crossing estimates into an actual wrong-key count. `VariableSeparator` supplies two-sided B2 crossing bounds for a specified ragged profile. Thus `badSend0` is conditionally available once one proves the stage-specific input tails and matches the profile cuts to the routed parent port; merely wrapping these three lemmas would not close the schedule obligation.

October 13 follow-up: `AdaptivePaddedWitness.output_slot_wrong_le` now packages the generic output step for either scale-specific separator. For any injective enumeration of a bag, any rank window `[L,H)`, and any target native interval, an input rank-window error `A` yields a wrong-key bound of `A + 2E`; the witness's two-sided crossing field supplies both boundary errors `E` directly. `AdaptiveRaggedSlotBridge.adaptive_ragged_parent_slot_wrong_le` composes this with `RaggedStageSlotBridge`: the selected physical parent down-port is exactly the local network's output slot, provided the local network and input enumeration are identified with the adaptive witness. Both theorems pass a focused Lean check. Thus the output-slot-to-routed-port seam is closed conditionally. The remaining higher-order `fringeSend` premises are the stage-specific input rank-window estimate from the outsider invariant and installation of a matching adaptive separator at every active bag. The separate root and frontier rules also remain open.

The higher-order field now has a symmetric local primitive: `TruncatedPaddedWitness.fLow_baseline` proves a multiplicative low-fringe estimate on the restricted live prefix using the flipped truncated certificates. Its premise is stricter than the high-side premise: the protected fringe must fit inside the actual live suffix, without padding allowance. The numeric fit is now derived from a `LocalIntegerFlow`: the address-debt bound gives ideal up-flow at least `(upFlow-ePos)*C`, rounding costs at most one wire, and the occupancy identity with `|eta|≤69` supplies `a≤C+69`. Thus the local low-fit inequality is closed from the scheduled-flow fields. Neither orientation is yet matched to the variable-width routed slots at every scheduled bag, and the later-stage two-tail input bounds must still be derived from `P(t)` and the global integer schedule. Thus `fringeSend` remains open; the signed-window theorem still assumes the stage-specific tails.

The earlier same-bag scale objection is resolved at the provider-existence level by `adaptive_padded_witness_exists`: the tuned width-16 branch covers `2^34 ≤ a < 2^38`, and the standard branch covers `a ≥ 2^38`. It supplies a common separator interface at the `2^34` minimum capacity, including the low-flow fit. This does not itself install a witness at each scheduled bag or establish its input rank-window premise; those remain global schedule/invariant obligations. `SAME-BAG-INTEGRATION-AUDIT.md` retains the historical analysis and should be read with this update.

Recommended proof order: (1) prove the exact number/range of late stages below the `2^38` witness threshold, and decide whether a separate terminal kernel absorbs them at bounded total depth; (2) if not, lower the local scramble-existence threshold while preserving both B2 and fringe contracts; (3) package the resulting witnesses with the ragged slot profile; (4) derive arbitrary-stage `hL`/`hR` from parent outsiders plus the schedule's prefix/suffix mass identities; (5) compose into `badSend0` and `fringeSend`. The low-fit arithmetic itself is no longer a separate risk. No `NodeSpec`-based all-stage argument currently closes these gates.

## Result and next step

The ordinary scalar induction is isolated and conditionally closes. The concrete routed ownership witness now supplies `PlacementStep.hregs`, and the exact interior source identity separates parent slots from child up-ports. Remaining ordinary gaps are the global integer schedule's cardinality/capacity invariants, lifting the local variable-window/NodeSpec estimates to every ordinary parent to prove `badSend0` and `fringeSend`, and handling terminal residual sends. Frontier transitions and global P remain separate. The new `RaggedTreeRoute` module was checked with Lean 4.29.0-rc4 against the existing focused scratch dependency cache; no full package build was run.

## October 13 flow-table composition gate

`GlobalFlowStep.lean` now proves the one-stage choice glue. Given an actual
current flow table and routed next partition, every next-stage active address
has an actual-cardinality `LocalIntegerFlow` if each frontier family's
actual register size is within 69 wires of its reference target. Interior
addresses use `candidate_interior_actual_flow_nonempty`; the generic
integerizer turns the frontier count discrepancy into a local flow. The
schedule classification routes all remaining addresses to the lower or upper
moving frontier. The chosen table is indexed once per address, so duplicate
parent descriptions cannot conflict.

This closes only the table-composition lemma. The remaining scheduler premise
is numerical: establish actual routed register sizes within 69 wires of
target for both moving-frontier families at every stage. The all-order key
outsider bounds must also be propagated on that same partition.
`AdaptivePaddedWitness.lean` supplies a common size-adaptive separator
interface, but its suffix/cohort conditions and the ordinary kernel's
stranger-count fields are not yet instantiated from the schedule.

`FrontierInteger.top_retreat_integer_split` now supplies a local rounded split
for the upper-frontier retreat under its proposed real mass and 69-wire
occupancy error. Along with top-advance rounding, this reduces the frontier
work to proving that actual routed counts follow those formulas and handling
the two lower-frontier transitions. No frontier rule has yet been installed
in a whole-stage route.

## October 13 input-tail derivation audit

`InvariantInputTails.lean` now proves the unconditional consequence of the
all-order outsider predicate for any active register: at order one, each tail
outside the bag's native interval is at most `mu * C`. For an arbitrary cut
inside that interval, the theorem adds the distance from the native endpoint
to the cut. The proof is kernel checked with Lean 4.29.0-rc4.

This does **not** provide the scheduled `hL`/`hR` inequalities. The gap term
can be much larger than a slot width, even on an ordinary active node. For
example, at `t=10`, `l=2`, and any `d >= 14`, `alpha=0`, `omega=4`, so this is
an interior scheduled level. Its reference capacity has exponent `6*d-36`,
while its native interval has exponent `6*d-12`. Thus the native interval is
`2^24 C`, and its first child interval is `2^18 C`. A set of about `C` keys
can lie wholly in that first child interval and still have zero outsiders at
every order relative to the level-two bag. The one-bag outsider information
therefore does not control the required first-cut mass (the signed separator
budget for slot zero is only about `rEnd*C`, plus the tiny up reserve and
rounding).

The missing input-tail proof must use the *global placement*: account for the
current register together with descendant storage and storage outside the
subtree. `FrontierRankCounting.ragged_rank_cut_recurrence` already isolates
the needed `D` lower bound on native descendant mass and `O` upper bound on
outside spill. `RaggedSlotMass` supplies abstract slot-error lemmas, but the
stage-dependent `D` and especially `O` premises are not yet proved from the
integer schedule and the routed ports. This is the live proof gate; extending
the one-bag interval estimate further cannot close it.

October 13 follow-up: the hierarchical bridges are now Lean-checked in
`OutsiderSlotMass.lean`, `OutsiderOutsideMass.lean`, and `OutsiderRankCut.lean`.
They derive descendant native mass and charge outside slots at their
ancestor-separation stranger order, then combine both with the generic
three-way rank count. `NativePrefixPartition.lean` proves the exact interval
identity for a prefix of whole native children. The new
`outsider_same_level_outside_native_mass_upper` also discharges separation for
distinct same-level bags. These are still conditional: cuts through a child
need recursive prefix coverage, and ancestor/frontier storage still needs a
schedule-derived bound. No actual global `D`/`O` instantiation or all-order
invariant induction has been closed.
`NativePrefixPartition.lean` now also kernel-checks `prefix_radix64_address`:
any cut in a native interval is a prefix of complete radix-64 child blocks plus
a remainder smaller than one child block. This provides the arithmetic index
for a recursive partial-cut proof, but the recursive Finset cover and its
weighted outsider-error bound have not yet been formalized.
The exact recursive cut interface has progressed one step: `native_prefix_one_child_decomposition`
proves that a prefix of any native bag is a union of complete child intervals
and one residual interval lying strictly inside the next child. The residual
length is below one child block. Repeating this identity gives the shape needed
for an exact hierarchical prefix cover; the repeated cover and its weighted
error estimate are still open.

## October 13 recursive budget and ancestor check

`RecursiveCutBudget.lean` now proves the analytic series bound: if the
canonical prefix decomposition contributes at most 63 completed sibling
registers at each descendant depth, and each is charged with its corresponding
higher-order stranger allowance, their total is at most
`mu * radixSiblingFactor`; the rational factor is below the candidate
`siblingFactor`. This is kernel checked. The missing combinatorial induction
must still build the multi-level prefix cover and prove the depth-r slots are
charged at stranger order r in the actual execution.

A crude cardinality bound does not close the ambient ancestor term. The first
active ancestor can have capacity `C/4096`, while the reserve is only about
`8.6e-8*C`. The intended useful estimate is the ancestor register's mass in a
particular descendant interval: its nominal uniform share is another factor
`1/4096`, about `C/16,777,216`, which is within the reserve scale. Establishing
that localized share requires a parent separator/rank estimate and then a
recursive argument for higher ancestors; total register size alone is
insufficient. Thus ancestor/frontier storage is still a major open gate.

## October 13 one-step ancestor localization screen

`AdaptivePaddedWitness.output_slot_wrong_le` is the available output bridge: it
bounds wrong keys in a child slot by an input rank-window error `A` plus two
crossing errors. The missing premise is a bound on `A` for a descendant
interval inside the ancestor's own native interval. `TaperedOutsiderBoundLe`
does not imply it: all keys in an ancestor register can be native to that
ancestor while concentrated in one descendant interval, and that ancestor's
own outsider clause would still hold. Other schedule/history constraints might
rule this out, but they have not been shown. The output B2 contract controls
crossings at the separator output cuts, not this internal input
concentration. Thus this localization requires a stronger historical/rank
invariant or a schedule argument beyond the current outsider predicate.

The scale screen is narrow but numerically feasible. At `(d,t,l)=(14,10,2)`,
the active level-two capacity is `2^48`, and the active root capacity is
`2^36 = 2^48/4096`. If the root-register mass in a selected level-two interval
is bounded by its ideal one-of-4096 share, `1/4096^2` of the target capacity,
then adding the width-16 crossing allowance
`epsB/4096 + (16*epsB+32)/2^48` remains below `reserve`. Lean theorem
`one_ancestor_localization_screen` certifies this rational inequality. The
coarse total-capacity allowance `1/4096` exceeds reserve by orders of
magnitude (`ancestor_total_capacity_exceeds_reserve`). This confirms the exact
risk: prove the internal input distribution, not merely the local output
crossing bound.

## October 13 explicit ancestor-profile contract

`AncestorLocalizationProfile.lean` now defines the missing stronger state
property directly: for a descendant native interval `q`, bound the mass from
each ancestor register inside `nativeKeys q`, with a bound depending on the
ancestor distance. The generic subregion theorem shows this also bounds every
prefix/cut contained in that interval. A second kernel-checked lemma makes the
blind spot precise: every subset of a bag's own native interval has zero
order-one strangers relative to that bag. Thus the per-bag outsider clause
cannot, by itself, force mass to be spread among descendants.

This is an interface, not a propagation proof: no theorem currently shows the
schedule establishes or preserves `AncestorLocalizationProfile`. The
existing `outsider_rank_cut_bound` already supplies the useful global accounting
once descendant native mass, incomparable outside spill, and an explicit
`ambient` bound are provided. Therefore the next proof gate is to use the
actual ragged route to bound ancestor/frontier ambient mass in each selected
prefix, and to show that this bound is preserved one stage at a time. At the
root-to-level-two test scale, an ideal uniform ancestor share plus the existing
separator crossing allowance fits the reserve, but the ideal share remains an
unproved schedule/rank-distribution estimate. No improvement to the 945
coefficient is established by this contract alone.

## October 13 scheduled subtree mass calculation

`TaperedSubtreeMass.lean` ports the Chvatal subtree-bad estimate to
`TaperedOutsiderBoundLe`: at each descendant depth it charges the lesser of
the tapered stranger allowance and the scheduled register size. It also
packages the exact ambient localization step: if the descendant subtree has
mass `nativeSize - D` and its nonnative spill is at most `O`, then any disjoint
ancestor/frontier register contributes at most `D + O` keys to that native
interval. Thus actual schedule work reduces to calculating subtree register
mass and evaluating the depth sum.

`TwoLevelSubtreeBudget.lean` checks the concrete two-level scale symbolically.
If the parent register is within 69 wires of `(1-1/cap) C` and each of its
4096 grandchildren is within 69 wires of `(1-1/cap) 4096 C`, their combined
subtree deficit from the native interval `cap*C` is `C/cap` with error at most
`69*4097`. At `C=2^48`, this rounding deficit fits the signed reserve. But the
generic subtree-bad sum includes the current node's order-one error `mu*C`,
and `reserve < mu`; that coarse bound cannot fit the reserve. This is a proof
accounting obstacle, not evidence that the schedule itself fails. The next
step is to separate the current node's native mass from its outsider tail in
the rank-cut accounting, so the tight reserve is charged only for the true
localized ancestor/frontier residue. These results are conditional and do not
yet instantiate the schedule or prove the 945 coefficient.

Follow-up: `tapered_strict_subtree_bad_le` now charges only strict descendants,
starting at stranger order two, and `tapered_strict_subtree_native_mass_lower`
turns that estimate into the descendant-mass premise required by the rank-cut
recurrence. `strict_subtree_keys_eq_sdiff` and `card_strict_subtree_keys` give
the exact complete-tree cardinality formula with the root register removed.
This avoids charging the current bag's order-one error in the D-side budget.
The additional `card_strict_subtree_keys_address_dependent` formula expresses
the mass as the sum of actual per-address register sizes, so the flow's
local routed-count recurrence can feed it without a uniform-level-size
assumption.
The unresolved O-side is still substantial: one must partition outside-prefix
storage into incomparable sibling registers (charged at their separation
orders) and ancestor/frontier registers (charged by a schedule-derived mass
defect). The local two-level defect certificate bounds the latter's nominal
rounding contribution, but a full level-count instantiation and the actual
outside-prefix cover are still missing.

October 13 routed outside-cover step: `RaggedRankRecurrence.lean` now proves
`raggedOutsideSubtreeKeys_eq_outside_bag_cover`. The O-side key set is exactly
the union of actual routed placement registers indexed by bags other than the
current bag and its strict descendants. This follows from completeness and
disjointness of `raggedPlacement`; it applies to the real routed execution,
not a uniform-flow model. It does not yet classify those bags as incomparable
siblings versus ancestors/frontier, or assign numeric capacities and rank-leak
bounds to the resulting families. Those remain the next gates, so the exact
cover alone does not establish that the reserve fits.

The tree classification is now formalized in `RaggedRankRecurrence.lean`:
`outside_bag_ancestor_or_separated` proves each outside bag is either a strict
ancestor or separates from the selected bag at the common ancestor level;
`raggedOutsideSubtreeKeys_subset_ancestor_separated_cover` turns that into a
cover by actual routed registers. `TaperedSubtreeMass.lean` also has a general
conditional counting lemma bounding any storage disjoint from the strict
descendant subtree by its mass defect plus the order-two-and-higher spill.
Together these identify the intended proof route, but the specialized bridge
from the actual ancestor-register cover into the generic outsider estimate is
not yet checked. Nor has the schedule supplied the exact identity
`nativeWireKeys.card = D + strictSubtreeRegisterMass`, the small defect and
spill budgets, or the separated-bag error sum. The D-side selected-slot lower
bound remains separate. No coefficient improvement is established here.

October 13 classification/localization follow-up: the outside-bag index set is
now partitioned into strict ancestors and bags separated at a common ancestor
in `RaggedRankRecurrence.lean`. The latter satisfy the exact separation
hypothesis used by `outsider_incomparable_outside_native_mass_upper`. In
`TaperedSubtreeMass.lean`, `ambient_set_native_bound_of_strict_subtree_mass`
extends the localized-count argument from one ambient register to any storage
set disjoint from strict descendants. `RaggedOutsideBudget.lean` specializes
this to the aggregate actual strict-ancestor registers, proving their prefix
mass is at most `D+B` given the exact subtree mass identity and the strict
higher-order spill budget. These three modules passed focused Lean checks.

The combined O-side theorem is still a proof obligation: the actual routed
cover must be instantiated in the generic outsider estimate and the resulting
ancestor and separated-bag budgets added. More substantially, the integer
schedule has not supplied the exact mass identity or shown the budgets fit the
reserve. Active frontier registers outside the strict ancestor chain remain
in the separated family and need the corresponding outsider charges. The
D-side selected-slot lower bound also remains open.

October 13 strict-tail arithmetic and seed audit: `TwoLevelSubtreeBudget.lean`
now includes a checked exact-rational certificate for the infinite strict-descendant tail. At depth `h`, the proposed envelope contributes at most `mu * (64^2 * delta)^h * C`; since `64^2 * delta = 1/8192`, the sum from `h=1` is `mu/8191 = 17/586191470592`, about `2.90e-11 C`. This is about `1/2957` of the signed reserve (`11783/137405399040`, about `8.58e-8 C`). The new theorem passed a focused Lean check. This closes only the numerical tail calculation, conditional on establishing the candidate capacity bound for every strict-descendant level actually included in the schedule.

The seed formulas confirm that this capacity hypothesis cannot simply be assumed at the moving frontier. At `(l,t)=(2,2)`, the exact seed count is `65535/2^24` of `candidateReferenceCapacity`; at `(l,t)=(3,3)`, it is `255/2^24`. These are intentional special bootstrap geometries (with local `NodeGeom` proofs), but they are far below the ordinary occupancy window. Consequently the geometric tail certificate does not by itself give the strict-subtree mass identity or a small defect for subtrees crossing those frontier states. The next proof gate is to isolate a schedule-valid start state/region for the mass argument, or to add a separate exact frontier-mass correction and show it is affordable. The coefficient and global O-side remain unproved.

October 13 bootstrap-mass identity check: `BootstrapMassAudit.lean` now proves
exact population identities for both special states. At the stage-two root,
`64^d = 64 * seedLevelOneUp + 4096 * seedLevelOneDown`: root occupancy plus
all level-two descendants exhaust the root population. At stage three, for
each level-one frontier interval,
`64^(d-1) = seedStageThreeTopSize + 4096 * seedBottomDown2`. The latter's
strict-descendant-only defect is exactly `candidateReferenceCapacity d 1 3`,
proved in `bootstrap_level_one_defect_is_reference_capacity`; the root defect
is likewise exactly its own stage-two register count. The module passed a
focused Lean check.

This rules out closing the signed-reserve gate by applying the present
whole-strict-subtree ambient-mass estimate directly at these bootstrap states:
its defect is one full reference-capacity unit, while the reserve is only
about `8.58e-8` capacity units. That is a method-specific obstruction, not a
counterexample to the sorting construction. The rank-cut recurrence already
has the better accounting shape: lower-bound selected child-slot mass and
charge only outside-prefix storage. The next useful proof work is to connect
actual frontier slot widths and their wrong-rank errors to that recurrence;
trying to shrink this whole-subtree defect would require a new rank-local
cancellation theorem.
