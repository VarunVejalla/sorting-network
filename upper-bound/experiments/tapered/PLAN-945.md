# Tapered-flow route to a sub-1000 sorting bound

Status: research ledger, not a theorem. The current candidate arithmetic suggests
a coefficient of `945` for `limsup D(n)/log₂ n` if the integer schedule,
separator invariant, and global recursive construction all close. The earlier
`945.006` figure included a terminal-profile surcharge from a flow model that
has since been replaced. Neither number is currently a proved sorting bound.
For the parameter screen and equations, see [`SUB1000-CANDIDATE.md`](SUB1000-CANDIDATE.md).

## Proof map and status

### Current checkpoint: local gates closed, global theorem still open

This checkpoint supersedes the older task descriptions below where they say
the output bridge or smaller-row bulk existence is missing.

| Component | Current evidence | Remaining obligation |
|---|---|---|
| Actual output counting | `SlotOutputBridge`, `SeparatorKeyBridge`, and `BootstrapSeparatorOutput` pass focused Lean checks. Actual execution ranks are identified with key-set ranks; the stage-one interior wrong-key estimate reaches the output. | Endpoint slots and later-stage input hypotheses. |
| Smaller-row bulk construction | `CandidateBulkWitness`, `CandidateBulkFail`, and `CandidateBulkProvider` pass focused checks. There are actual two-round B2 witnesses in both orientations for rows at least `2^34`, columns at least 16. | Feed the actual cut and rare-rank interfaces into the recursive outsider induction. |
| Arbitrary live sizes | `AnyCutBounds`, `RectanglePadding`, `PrefixPadding`, and `PaddedSeparator` pass. `BaselineFringe` proves a multiplicative rare-rank guarantee after restriction, conditional on truncated F2 witnesses. | Prove the selected suffix contains `f+1` protected rows at every scheduled bag, then use it in the global induction. |
| Wire ownership/execution | `RaggedWireOwnership` and `RaggedExecution` pass. Unequal wire slices can be routed as a genuine partition, and simultaneous depth is bounded by the largest local depth. | Choose the address-specific integer flows coherently at every stage. |
| Exceptional frontier mass | `FrontierDebtFlow`, `FrontierPositivity`, `FrontierInteger`, and `SubtreeMass` pass: static-debt conservation/positivity, integerizable top advance, and exact complete-subtree cancellation. | Integerize other frontier motions; derive rank bounds for partial cuts and prove the meeting rule. |
| Price and termination | `WireRoundingBudget` checks a conservative scalar allowance; `Fallback999` checks a conditional 999 scalar price. `TaperedTerminal` proves a conditional parent-group finishing sorter of additive depth 903 from order-two purity. | Charge actual frontier/invariant terms and prove the complete eventual depth recurrence. Neither 945 nor 999 is a sorting theorem. |

The critical remaining mathematical gates are:

1. **Compatible fringe witnesses:** prove actual failure fractions for the
   truncated scrambles and combine them with the full-row bulk pair. This is
   now proved in `TruncatedScrambleMeasure` and `TruncatedFringeProvider`.
   `TruncatedPaddedProvider` packages a real padded pack of depth ≤1890 whose
   same scrambles satisfy B2 in both orientations and the truncated SR/R1/R2n
   contracts in both orientations. `TruncatedPaddedWitness.fHigh_baseline`
   transfers the high-side rare-rank estimate to a restricted live bag,
   conditional on its actual fringe suffix size and cohort range. The
   low-side transfer is not yet formalized: it must turn flipped semantic F2
   into a physical low-tail count and then restrict to the live prefix.
2. **Frontier rank cancellation:** instantiate `SubtreeMass` at actual key
   sets. Complete subtrees cancel exactly; `FrontierPrefixMass` carries that
   identity across any prefix of whole child subtrees, and
   `FrontierRankCounting` gives the three-way counting bridge. Cuts through a
   child still need the recursive outsider budget and an actual instantiation.
3. **Global induction and integerization:** assemble seed, interior, and
   frontier rules into one recursive allocation; prove all-order outsider
   bounds for its actual execution.
4. **Terminal sorting and endpoint:** order-two purity suffices to sort
   parent groups at termination; then price the complete network, prove an
   eventual depth bound, and audit headline axioms.

The best verified global endpoint remains **1419**. All work here stays in
the experiment; promotion requires the user's review.

Additional gates checked in this work session: `FrontierRankCounting` passes
as a generic disjoint-storage/three-way cover lemma; `FrontierPrefixMass`
passes for every prefix of whole child subtrees; `BaselineFringe` passes with
explicit truncated F2 hypotheses; `TruncatedScrambleMeasure` preserves exact
failure fractions under one-row truncation; `TruncatedFringeProvider` proves
simultaneous bulk/fringe scramble existence; `TruncatedPaddedProvider` packages
the actual same-pair padded separator and its conditional high-fringe estimate;
and `TaperedTerminal` passes with the recursive order-two purity hypothesis.
See the modules for exact statements.

The separator's remaining interface gates are now explicit: prove each
scheduled suffix fits the high fringe condition
`(f+1)*columns ≤ u + padding`, keep its cohort within `jmax`, and establish
the corresponding low-side live-prefix fringe estimate. These are downstream
of the global integer scheduler; none follows from the padded witness's
existence alone.

| Module | Checked result / status | What remains | Dependency / gate |
|---|---|---|---|
| **A. Variable-width window algebra** | `VariableSlots.lean` and `VariableWindow.lean`: unequal child widths; separate left/right rank tails; per-slot transfer from native mass plus outsider budget; signed endpoint/interior reserve estimates. | Instantiate the cumulative native-slot bounds and outsider budgets from the actual schedule. | Needs the schedule-specific invariant in D; this is an interface, not a separator theorem by itself. |
| **B. Signed flow and integer rounding** | `SignedReserve.lean`, `AddressDebt.lean`, `IntegerRounding.lean`: candidate signed-debt bounds and uniform real occupancy identity; a one-step even natural up-flow and 64 child blocks with exact total under explicit hypotheses. At `C ≥ 2^34`, `|η| ≤ 69`, and the candidate split equation, adjusted targets are positive and the next discrepancy is below 69. | Prove all premises for every active bag, including exceptional levels; choose a globally coherent witness rather than a fresh unrelated witness per local application. | Depends on the globally defined scheduler in C. Local integerizability is not global realizability. |
| **C. Frontier and seed arithmetic** | `CandidateFrontier.lean`: active-window ordering, successor closure, and one-level frontier motion. `CandidateSeed.lean`: exact seed counts/placements through stage 2 and a bootstrap table through stage 3; root, level-one, and both stage-two sender types have `NodeGood` providers. `RaggedBootstrapGeometry.lean` gives the exact address-dependent stage-one row profile and average `NodeGeom`; `RaggedResetGeometry.lean` gives all four stage-two sender geometries with common down-flow. | Connect the ragged row profiles and local-network providers to the actual address-indexed placement. Extend the flow table beyond the finite reset, with coherent moving-frontier and terminal rules. | Geometry and count conservation are checked, but do not construct a placement with ragged child blocks or determine their ranks. |
| **D. Global address-indexed integer scheduler** | `RaggedIntegerSchedule.lean`: ordinary interior active successors remain scheduled; given current local flows, routed discrepancy is ≤69 and a next local flow exists. `RaggedBootstrapFlow.lean` packages the stage-one ragged profile. `RaggedResetFlow.lean` packages the root's zero-fringe stage-two profile and proves exact stage-three top/bottom counts. | Replace the separate finite row/count tables and conditional interior step with one coherent address-indexed placement/scheduler. Prove exact wire ownership, nonnegativity, capacities, address coverage/no duplication, and root/frontier/terminal rules. | These local tables are not a `FlowSizes` replacement or a global scheduler; the standard type has one down-count per level/time and cannot express the varying widths. |
| **E. Two-sided outsider induction (main mathematical gate)** | `VariableSeparator.lean` proves two-sided B2 estimates at arbitrary row-aligned ragged cuts; `RaggedFlowContract.lean` packages the profile and both fringes. `AddressDebt.lean` proves signed cumulative-width budgets and a local bootstrap integerizer. `RaggedStageOneRank.lean` proves actual stage-one input tails. `StageOneWindowGate.lean` proves the exact population split and `candidate_bootstrap_stage_one_wrong_rank_bound`, composing those tails with the signed window theorem. | Connect the input wrong-rank count to the ragged separator's actual output using its two boundary crossing bounds. Extend this into later stages and a coherent scheduler. | The input-tail, population, and joint rank-window gates are kernel checked, conditional on the root `NodeSpec`. The placement-to-rank/output interface remains open; the variable-width profile is not installed in a global scheduler. No stage-one-to-stage-two outsider transition or global bound follows yet. |
| **F. Root, moving frontiers, and terminal bags** | Exact root-to-stage-2 counts and local sender networks are checked. Stage 2→3 conservation and capacity matching are checked. The raw input root exceeds the ordinary ≤69 discrepancy range (`candidate_raw_root_exceeds_interior_target`). | Prove the root and frontier rank invariant, continue local network/flow availability through later frontier shifts, and set a valid stopping condition whose bags can be sorted within the charged depth. Bound exceptional work on every path. | Root geometry alone is not the outsider base case. Stage-3 capacity matching is count-only; it does not imply stage-3 sender geometry or terminal sorting. |
| **G. Recursive sorting network and depth recurrence** | Existing components provide local networks, depth facts, and the two-round separator interface, but the tapered candidate is not yet a complete recursive sorter. | Assemble the finite recursive network; prove it sorts every input, handles all arities (including padding/restriction), terminates, and bounds maximum path depth including roots, frontiers, and terminal sorters. | Requires E and F. Correctness and maximum-path depth must be proved together with the actual variable bag sizes. |
| **H. Constant and asymptotic endpoint** | Current candidate price is 3 stages at 1890 layers per six input bits, i.e. 945 layers per `log₂ n` bit for ordinary stages, subject to the candidate's exact parameters. This is a conditional leading-cost calculation. | Recompute the complete recurrence from G, including finite/root/terminal overhead and ceilings; prove an eventual bound `D(n) ≤ c log₂ n + b` with `c < 1000` (target 945 if the ledger survives); derive the limsup theorem. | Only follows from G. Do not infer the endpoint from the local stage price. |
| **I. Package verification / possible promotion** | Focused direct Lean checks with Lean `v4.29.0-rc4` passed for the arithmetic, seed, separator/window, ragged-flow/geometry, and conditional rank-interface modules in dependency order. | Once H exists, run the tapered package build and its axiom audit; then review dependencies and only afterward consider porting. | No full Lake build, headline theorem, or axiom-guard result for this candidate is recorded. Nothing here has been promoted to `upper-bound/best`. |

## Dependency order and decision gates

```text
A window algebra ───────────────────────────────┐
B signed flow + rounding ──┐                    │
C frontier + seed arithmetic ──> D global schedule ──> E outsider induction
        │                    │                         │
        └─> F root/frontier/terminal rules <───────────┘
                                                   │
                                      G recursive sorter/depth
                                                   │
                                      H coefficient + limsup
                                                   │
                                      I build/axiom audit
```

The root-to-level-one outsider estimate is formalized, conditional only on
the root's `NodeSpec`, and fits the candidate's `mu * capacity` budget. The
actual level-one input tails at every internal ragged cut are now bounded by
that root outsider budget plus the exact signed address-profile slack. The
first ragged sender geometry, four stage-two sender geometries, root stage-two
ragged allocation, and exact stage-three count reset are also formalized. The
`candidate_bootstrap_stage_one_wrong_rank_bound` now composes the input-tail
and card-split results into the variable-window wrong-rank count (focused Lean
check passed). The next missing step is a theorem connecting that rank count
to the ragged network output. The standard `FlowSizes` and
wire-placement model still cannot encode these varying blocks. This is a
closed input-tail gate, not a sorting theorem.

## What the present Lean results do and do not establish

- The local arithmetic and interfaces are kernel checked under their stated
  hypotheses. In particular, the one-step integerizer and the interior
  successor-flow result do not select one schedule consistently across the
  whole tree.
- The two-round separator boundary lemma is about its physical pack at ragged
  cuts. It does not supply the address occupancy premise or prove a subtree
  outsider bound.
- `RaggedBootstrapGeometry.lean`, `RaggedResetGeometry.lean`, and
  `RaggedResetFlow.lean` prove compatible finite geometry/count equations.
  `RaggedFlowContract.lean` gives cut bounds once a physical pack and row
  profile are supplied; it does not install that profile in the current
  execution semantics.
- `RaggedStageOneRank.lean` proves the actual stage-one hL/hR input-tail bounds
  and root-native tail budget, conditional on the root `NodeSpec`;
  `StageOneWindowGate.lean` proves the corresponding cardinality split and
  composed wrong-rank bound: twice the scaled root tail budget plus
  `reserve * seedRootDown d`. The map from this input rank count to the ragged
  network output remains open.
- `CandidateSeed.lean` proves count/placement flow through stage 3, the
  root-to-level-one outsider bound and its candidate-budget comparison, exact
  zero descendant mass below level two at stage one, and actual
  `NodeGood` network existence for the root, level-one bag, and both stage-two
  sender shapes. The stage-one-to-stage-two rank/outsider transition remains
  open, and the stage-3 matching does not establish later sender geometry.
- The ordinary root cannot satisfy the interior discrepancy hypothesis
  directly. A proved root funnel is mandatory.
- Therefore there is currently no complete sorting theorem at 945 (or any
  sub-1000 coefficient) in this experiment. The best verified repository
  endpoint remains the separately maintained `upper-bound/best` package.

## Verification scope

### October 12: internal stage-one rank-window gate

Focused direct Lean checks passed for `StageOneWindowGate.lean` and
`VariableSlots.lean`. The former now bounds actual input wrong ranks at each
internal address `1 ≤ j ≤ 62`. The latter's `VariableRankSlotSpec` now describes
a particular output permutation, rather than incorrectly requiring the
boundary guarantee for every arbitrary permutation. No other source currently
uses that interface.

Next prove that wrong keys in an output slot are covered by the input's
wrong-rank keys and its two boundary crossing sets. Use injectivity of the
output rank permutation to charge the first set, and the existing physical
ragged pack estimates for the crossings. Then instantiate this counting bridge
with the actual key-to-local-rank bijection and bootstrap profile. Endpoints,
later stages, and the global scheduler remain separate obligations.

The focused scratch checks above used direct Lean invocation against cached
dependencies. `lake env` attempted a GitHub dependency fetch in a network-
restricted environment, and neither the complete tapered Lake package nor the
best package was rebuilt for this ledger update. Re-run focused checks after
source changes; run the full candidate build and axiom audit only when the
recursive theorem is assembled. Keep all scratch work in this experiment until
the proof and endpoint have been reviewed; this plan does not authorize
promotion or a commit.
