# Global cost audit and research decisions

Research review, 2026-10-10. No new sorting bound is proved here. The checked
endpoint remains `limsup D(n)/log_2(n) <= 1770`. This audit reads the existing
proofs and separates complete conditional budgets from unconstructed primitives.

## Reports

- [Paterson requirements and costs](paterson.md).
- [Chvatal requirements and costs](chvatal.md).
- [Persistent sorted cores](structured-cores.md).
- [Final-round repair findings](repair-investigation.md), including the
  [threshold contract](repair-contract.md) and [candidate audit](repair-candidates.md).
- [Lossless fringe capture](lossless-fringe.md): a correction to the compaction
  premise and a deterministic cyclic small-rank construction, with bulk
  compatibility still open.
- [Joint small-rank capture and bulk mixing](joint-small-rank-bulk.md): an
  informal reduced-witness counting proof for independent random rows at
  `f>=131040`, including a bound uniform in the number of columns.
- [Two-round relative fringe](two-round-relative-fringe.md): an informal
  moderate-inner-fringe and reduced-tail-witness argument covering unbounded
  supported ranks at `f=262080`, with the final repair still unconstructed.
- [Repair ancestor obstruction](repair-cone-obstruction.md): the enlarged
  tail-promise class requires at least 26 column-local repair layers, exceeding
  the 19 left by the larger template height budget.
- [Reachable height envelope](reachable-height-envelope.md): a stronger
  informal common-witness property excluding that obstruction's tall-column
  state, and an explicit record of the unsuccessful smaller-fringe estimates.
- [Aggregate tail interface](all-scale-tail-interface.md): an informal common
  dyadic-tail guarantee excluding the many-column witness and a fixed-window
  fringe construction whose current bitonic depth is still too expensive.
- [Fixed-window capture audit](fixed-window-capture-audit.md): costs of halver
  and run-merge candidates, and a bulk obstruction to block-constant scrambling.
- [Fresh-reservoir funnels](fresh-reservoir-funnels.md): an explicit 86-layer
  candidate meeting the fringe error in fixed-input expectation; a universal
  common-witness theorem and bulk repair remain open.
- [Tournament pair witnesses](funnel-pair-witness.md): pair and root-density
  estimates reduce expected error to about 40% of the target, at the same depth; shared
  dependency graphs remain the obstacle to a universal failure bound.
- [Disjoint bulk budget](disjoint-bulk-budget.md): rank-sensitive first-round
  estimates handle the edge cuts and protect edge windows, allowing a proposed
  central bulk repair to run in parallel with the funnels within 107 layers.
- [Exact funnel count transitions](funnel-count-transition.md): a conditional
  generating-function formula accounts for shared tournament groups within a
  fixed column; the subsequent joint-tail note handles joint columns, while
  reduced-profile estimates remain open.
- [Joint funnel tail](funnel-joint-tail.md): an elementary negative-association
  argument supplies the joint-column mgf inequality and a fixed-input
  exponential failure bound; the reduced-profile union still remains open.
- [Central bulk feasibility](central-bulk-feasibility.md): explicit band
  localization, a smaller restricted-profile entropy count, and a 631-layer
  bulk baseline; neither narrow bands from L1 alone nor preserved long runs
  currently supplies the desired 107-layer repair.

## Complete budget comparison

| Construction with its scheduler retained | Conditional coefficient | Requirement for a strict bound below 1000 |
| --- | --- | --- |
| Legacy Paterson | `6.5*s + r + 1` | With checked `r=561`, a complete scheduled separator of depth `s<=67` gives `997.5` |
| Chvatal | `T/2`, for ordinary-stage depth `T` | Every ordinary node, including fallback cases, must have depth `T<=1999` |

For Paterson, `s` includes the rare-rank tail guarantee, large-cohort first
split, partial bags, padding, and physical routing. It is not the depth of an
isolated halver. For Chvatal, `T` includes both orientations, bulk and fringe
requirements, all supported ranks, one common scramble witness, and the
physical comparator implementation.

The checked costs are `s=989,r=561` (Paterson: `6990.5`) and `T=3540`
(Chvatal: `1770`). Root-only Paterson improvements leave a coefficient of at
least `6429.5` in this accounting. Chvatal root and terminal improvements affect
only the additive term.

## What the audit rules out

1. **Repair-only Paterson work cannot reach these targets.** Even free root
   repair leaves the expensive interior separator unchanged.
2. **Optimizing the current one-round Chvatal fringe probability cannot reach
   1000 with the current bitonic implementation.** Its deterministic fringe
   obstruction and scheduler geometry already force too large a column height.
3. **Three full sorts at height `2^42` do not reach 1000.** They cost `2709`
   layers per stage, yielding `1354.5`, conditional on still-unproved joint
   fringe and bulk guarantees. Template rounding may raise this further.
4. **Sorted-core reuse has two separate obligations.** Merge preserves run
   sortedness, but need not preserve extreme capture after exchanging keys.
   Repeated logarithmic-depth merges with constant-factor error contraction
   can also cost quadratic logarithmic depth. Both correctness and amortization
   must be established.

These are barriers to the specified constructions and accounting, not lower
bounds on sorting-network depth.

## Recommended next work

The first task should be a precise **final-round repair interface for Chvatal**.
It offers a direct connection to the stronger existing global endpoint. Do not
start by assuming that a cheaper repair reproduces a full column sort.

State what a second scramble leaves in each column and exactly which threshold
counts a replacement must correct to deliver the scheduler's bulk and fringe
fields. Quantify over all admissible intermediate states, all supported ranks,
both orientations, and the same fixed network. Prove the count implications
before attempting its comparator construction.

The budget is unforgiving:

- At column height at most `2^42`, two bitonic sorts cost `1806`; a third-stage
  replacement must cost at most `193` for a strict sub-1000 coefficient.
- At height at most `2^43`, two sorts cost `1892`; only `107` layers remain.
- These budgets must also cover any additional charged routing. The ordinary
  small-node fallback must be reduced: its current `2016` bound is too large.
- The exploratory bulk calculation uses `1/59000000`; the current `NodeSpec`
  uses the smaller `paperOrdinaryEpsB`. Use the actual budget or prove a change
  to the scheduler's specification. Do not silently substitute the weaker one.

In parallel, the Paterson alternative merits one bounded feasibility study:
can a graph-based separator meet the **whole** scheduled contract within 67
layers? Derive the expansion/execution requirements for the simultaneous
large-cohort and rare-rank guarantees, including partial support, and charge all
refinement and routing layers. A shallow rare-rank halver alone is insufficient.

Persistent cores should remain a smaller auxiliary investigation: prove or
refute the one-pair all-rank closure statement in [the report](structured-cores.md).
Even a positive result needs an initialization and scheduling argument before
it becomes a global improvement.

## Target near 200

Neither audited construction currently has a credible complete path to 200.
Chvatal needs an ordinary stage of at most 400 layers; even one height-`2^42`
bitonic sort costs 903. Paterson would need both a much cheaper separator and
root partitioner, for example the conditional pair `s=24,r=43` gives exactly
200. These numbers specify obligations, not constructions.

A plausible direction is to co-design a shallow approximate separator with a
global invariant that tolerates and contracts its error, while avoiding full
sorts of large cores. Its acceptance criterion should be a complete depth
recurrence and correctness interface first. A claim based only on a local
mixing rate, an uncharged exact-selection oracle, or assumed interleaving is
insufficient.

## Verification scope

The reports were prepared in parallel and reviewed against the existing source
and earlier experimental notes. No Lean files or production packages were
changed, and no build or axiom check was run for this documentation-only audit.
All new interfaces and substituted cost formulas remain informal.

- [Profile-budgeted funnel recurrence](profile-budgeted-funnels.md): couples exterior errors and fresh-root blockers under one tail-mass budget; a local numerical diagnostic has large expectation slack but does not resolve profile entropy.

- [Central 107-layer candidate screen](central-107-screen.md): the published two-layer k-halver is one-cut and its straightforward Batcher simulation already exceeds 107 layers at useful arity; a finite p-way parameter check is the next diagnostic.

The finite Batcher-priced screen finds k=512 as the largest power-of-two arity whose two k-sorter rounds fit 107 layers (90 layers, leaving 17 for p-way combination); its arbitrary-input halver error remains percent-scale.

The row-scramble-specific audit now gives a two-height profile on which the 2-round k=512 core leaves expected leakage at least delta/4 for every fixed second permutation. A final 17-layer p-way repair must contract this by about 110x; the profile is in the L1 class but not yet shown reachable after the first scramble.

Under the aligned two-height profile, a random-matching-only 17-layer finisher leaves about 0.0418 delta expected error; independent exact Batcher sorts of 32-wire blocks leave ~0.06998 delta. Both exceed the ~0.0022 delta stress threshold for this profile. Since the profile is not known reachable after the fixed scramble, this comparison motivates either better pooling or a sharper reachable-state analysis; it is not yet a necessary error bound.


A matching-graph screen sharpens the 17-layer localized-repair requirement: under the aligned iid boundary profile, degree 17 leaves an isolated-high contribution of `(1/4)*(3/4)^17 ~= 0.001879*delta`, leaving only about `0.000321*delta` of expected-error margin under the conditional `0.0022*delta` stress threshold. Sampled local cyclic-shift schedules leave roughly `0.044*delta`; these are simulation diagnostics, not universal lower bounds. See the matching-graph section of [the central screen](central-107-screen.md).

A distribution-trained fixed 17-layer matching schedule at 64 positions validates at residual `0.047394`, versus `0.051465` averaged over five random schedules; it remains over 21x the target and shows training overfit. The next diagnostic is to compare this prescribed greedy schedule with per-input maximum matching, separating graph capacity from edge-order loss. Reproduce with [matching_schedule_screen.py](matching_schedule_screen.py); the result is only for the iid two-row model.

A larger capacity screen on four random degree-17 bipartite multigraphs (4,096 positions, 500 balanced samples each) separates graph capacity from fixed edge order: fixed schedules leave about `0.0436` high defects per position, while input-dependent maximum matchings leave `0.00250`--`0.00261`. The latter is close to the `0.0022` conditional stress threshold; the fixed schedule is about 20x worse. This is a finite iid diagnostic, not a network construction. See [matching_capacity_screen.py](matching_capacity_screen.py) and the central screen.

A within-row butterfly compactor gives a stronger localized-pooling candidate: exact four-state propagation predicts `0.007920` residual on `2^16` positions using 16 compaction layers plus one cross-row layer. Exhaustively placing the 17th layer among the butterfly dimensions only improves this to `0.007162`; the best schedule in the whole 17-layer butterfly/cancellation family remains 3.25x above the conditional `0.0022` stress threshold. Perfect compaction would leave only the high/hole count imbalance, about `0.001102` per position. This shows room under the iid stress model, not that `0.0022` is required for reachable scheduler states. See [the exact screen](butterfly_compaction_screen.py) and the central analysis.

An initial screen of unstructured random perfect matchings is worse: on 256 wires, 16 random compaction layers plus final cancellation leave `0.047`--`0.051` leakage over the sampled schedules, compared with `0.029449` for the exact best 17-layer butterfly/cancellation schedule. This is only a three-schedule Monte Carlo check per orientation, not a lower bound on designed topologies. See [the random-network screen](random_compaction_screen.py).

A 16-layer prefix of a bitonic sorting network is also weaker: sampled leakage is about `0.0495` on 64, 256, and 1,024 wires, all above the butterfly-family result at 256. Generic random or sorting-network topologies do not solve the block compaction target; a distribution-tailored coarse-to-fine design remains needed. See [the bitonic screen](bitonic_prefix_screen.py).

Finite sorter-search tools can help generate small candidate gadgets, but their usual objective is exact full sorting (e.g. [SorterHunter](https://github.com/bertdobbelaere/SorterHunter), up to 64 wires). Tiling a perfect 64-position compactor per row still has an ideal iid imbalance floor of `0.03519`, so finite networks matter only as parts of a multiscale profile-combining construction. The `0.0022` figure above is a conditional stress threshold, not a proven necessary error for reachable scheduler states; see the central screen and exact [repair contract](repair-contract.md).

The 631-layer band baseline had a small reserve mismatch when paired with the `2048*n` protected-window error: its old band bound exceeded `E_B-2048` by 984-1516 per column at the two height endpoints. A cut-sensitive tail bound permits a `896*n` window allowance; slightly lowering beta then leaves at least 128 counts per column under the conservative bulk allowance and retains numerical probability margins over all 63 cuts. This is an informal parameter audit, not a closed probability proof; details and reproduction are in [central bulk feasibility](central-bulk-feasibility.md) and [the script](central_slack_envelope.py).

The finite matching-layer search now has a reproducible iid-proxy baseline: `finite_repair_search.py` and `results/finite-repair-64.json`. It improves a 64-position 17-layer schedule's iid residual from 0.04525 (repeated butterfly) to 0.02138 on held-out samples. This remains exploratory and is not a certificate for the scheduler's reachable localized profiles; see the added section in `central-107-screen.md`.

For exact finite-profile screening, see `cut_contract_screen.py`. It computes the per-cut `Q_*`, repaired count, and integer slack over an exhaustively enumerated L1/tail profile envelope under one fixed row scramble. A toy worst-case search found a 4-layer network passing 781 small cases when allowed to use all rows; the same shallow search constrained to a central subrectangle did not pass. These are search diagnostics only; details and JSON schedules are in `central-107-screen.md` and `results/`.

The contract-aligned screen separates the exact row-scramble images from the upstream profile reachability question, reports exact cut slack, and supports comparator search with a central-row restriction. Small unrestricted matches can use protected wires; enforcing the central region has so far prevented the toy search from passing. Those are finite search outcomes only.
