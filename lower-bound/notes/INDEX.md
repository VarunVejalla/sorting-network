# Lower-bound notes index

The lower-bound notes stay in [`docs/`](../../docs) because the scripts write their JSON results there by default and
the notes cross-link each other. This page indexes them by topic, with each note's scripts, Lean modules, status and
ticket.

Paths are abbreviated:

| Short form | Directory |
|---|---|
| `S:` | `lower-bound/experiments/scripts/` |
| `L:` | `lower-bound/experiments/AKS/Kahale/` |

Each Lean module has an `*Axioms.lean` guard where one exists. Every result JSON is `docs/kahale-<topic>*-results.json`
or similar. Do not open the JSON files whole: they are large exact catalogues.

Ticket statuses live in [`../backlog/tickets.json`](../backlog/tickets.json). The overview is
[`../backlog/SURVEY.md`](../backlog/SURVEY.md) and the barriers are in
[`../backlog/ruled-out.md`](../backlog/ruled-out.md).

## Endpoint and plan

| Note | Content | Status |
|---|---|---|
| [kahale-lower-bound.md](../../docs/kahale-lower-bound.md) | Proof map of the checked endpoint (`lower-bound/best`) | kernel-checked |
| [kahale-proof-plan.md](../../docs/kahale-proof-plan.md) | Loss decomposition, slot-saving conversion `2/(1-ρ)`, stop conditions; script `S:kahale_rank_entropy.py` | plan (LB-26) |

## Scalar relaxations: barriers to the existing method

| Note | Scripts / Lean | Status |
|---|---|---|
| [kahale-method-barrier.md](../../docs/kahale-method-barrier.md) | `S:kahale_height_barrier.py`, `L:MethodBarrier` | rejected, LB-20 |
| [kahale-positional-barrier.md](../../docs/kahale-positional-barrier.md) | `S:kahale_positional_barrier.py`, `L:PositionalBarrier` | rejected, LB-21 |

## Certificates: zero/one, pairs, potentials

| Note | Scripts / Lean | Status |
|---|---|---|
| [kahale-certificate-families.md](../../docs/kahale-certificate-families.md) | `S:kahale_certificate_probe.py`, `L:CertificateCompatibility`, `docs/kahale-certificate-witness.json` | parked, LB-22 |
| [kahale-union-coupling.md](../../docs/kahale-union-coupling.md) | `L:UnionCoupling`, `L:RankCrossing`, `L:ActiveWidth` | parked, LB-22 |
| [kahale-two-sided-heights.md](../../docs/kahale-two-sided-heights.md) | `S:kahale_two_sided_heights.py`, `docs/kahale-two-sided-heights-output.txt` | rejected, LB-02 |
| [kahale-joint-potential.md](../../docs/kahale-joint-potential.md) | `S:kahale_joint_potential.py`, `L:JointPotential` | rejected, LB-23 |
| [kahale-weighted-union.md](../../docs/kahale-weighted-union.md) | `S:kahale_weighted_union.py`, `L:PairUnionRecurrence` | rejected, LB-24 |
| [kahale-suffix-potential.md](../../docs/kahale-suffix-potential.md) | `S:kahale_suffix_potential.py` | rejected, LB-24 |
| [kahale-pair-union-rate.md](../../docs/kahale-pair-union-rate.md) | `S:kahale_pair_union_rate.py`, `docs/kahale-pair-union-rate-output.txt` | rejected, LB-24 (rate barrier) |
| [kahale-correlation-potential.md](../../docs/kahale-correlation-potential.md) | `S:kahale_correlation_potential.py`, `docs/kahale-correlation-potential-output.txt` | rejected, LB-33 (Harris = sizes; BK vacuous) |
| [kahale-amplification-kill.md](../../docs/kahale-amplification-kill.md) | `S:kahale_amplification_kill.py`, `docs/kahale-amplification-kill-output.txt` | rejected, LB-35 (sharpness potentials; no proved rate barrier) |
| [kahale-worst-case-inputs.md](../../docs/kahale-worst-case-inputs.md) | `S:kahale_worst_case_inputs.py`, `docs/kahale-worst-case-inputs-output.txt` | rejected, LB-34 (mixed polarity adds no witness; tree family tests one network; no coefficient) |
| [kahale-information-screen.md](../../docs/kahale-information-screen.md) | `S:kahale_information_screen.py`, `docs/kahale-information-screen-output.txt` | rejected, LB-03 (waste forced by `(n, d)`; marginal form false; true `h_g` form is LB-26; no coefficient) |

## Congestion and routing

| Note | Scripts / Lean | Status |
|---|---|---|
| [kahale-rank-congestion.md](../../docs/kahale-rank-congestion.md) | `S:kahale_rank_congestion.py`, `L:RankCongestion` | parked, LB-25 |
| [kahale-congestion-rate.md](../../docs/kahale-congestion-rate.md) | `S:kahale_congestion_search.py`, `L:CongestionBarrier` | parked, LB-25 |

## Information accounting (entropy, banks, transfer)

| Note | Scripts / Lean | Status |
|---|---|---|
| [kahale-target-four.md](../../docs/kahale-target-four.md) | `S:kahale_rank_entropy.py`, `L:RankInformation`, `L:ComparisonTrace` | parked, LB-26 |
| [kahale-swap-charging.md](../../docs/kahale-swap-charging.md) | `S:kahale_sorted_block_fibers.py`, `L:RankFiberMerge` | parked, LB-26 |
| [kahale-layer-bank.md](../../docs/kahale-layer-bank.md) | `S:kahale_layer_bank.py`, `S:kahale_relative_order_bank.py`, `S:kahale_relative_order_challenge.py`, `L:LayerBank`, `L:RelativeOrderBank`, `L:AmortizedAccounting` | parked, LB-26 |
| [kahale-boundary-transfer.md](../../docs/kahale-boundary-transfer.md) | `S:kahale_boundary_information.py`, `S:kahale_boundary_transfer_probe.py`, `L:ComparatorBoundary`, `L:ComparatorInformation`, `L:PermutationCompletion`, `L:RelativeOrderCode` | parked, LB-26 |
| [kahale-transfer-charging.md](../../docs/kahale-transfer-charging.md) | `S:kahale_transfer_localization.py`, `L:BoundaryTransfer`, `L:ComparatorTransfer`, `L:InsertionFibers`, `L:EntropyMonotonicity`, `L:LocalizedCharging`, `L:FiniteEntropy`, `L:FiniteFibers` | parked, LB-26 |
| [kahale-rankset-transition.md](../../docs/kahale-rankset-transition.md) | `S:kahale_rankset_transition.py`, `L:RankSetTransition`, `L:CrossingHistory`, `L:HistoryInnovation` | parked, LB-26 |
| [kahale-hierarchy-layer.md](../../docs/kahale-hierarchy-layer.md) | `S:kahale_hierarchy_layer.py`, `L:HierarchyRefinement` | parked, LB-26 |

## Occupation, activation, preparation

| Note | Scripts / Lean | Status |
|---|---|---|
| [kahale-layer-occupation.md](../../docs/kahale-layer-occupation.md) | `S:kahale_layer_occupation.py`, `L:OccupationLayer`, `L:OccupationCounterexample` | rejected, LB-27 |
| [kahale-degree-recycling.md](../../docs/kahale-degree-recycling.md) | `S:kahale_degree_recycling.py`, `S:kahale_conditional_certificates.py` | rejected, LB-27 |
| [kahale-joint-groups.md](../../docs/kahale-joint-groups.md) | `S:kahale_joint_groups.py`, `S:kahale_joint_slice_sat.py` (Z3) | rejected, LB-28 |
| [kahale-activation-scales.md](../../docs/kahale-activation-scales.md) | `S:kahale_activation_scales.py`, `S:kahale_sorted_block_activation.py` | rejected, LB-28 |
| [kahale-certificate-preparation.md](../../docs/kahale-certificate-preparation.md) | `S:kahale_certificate_preparation.py`, `S:kahale_fixed_antichains.py` | rejected, LB-28 |

## Residual images and witness charges (latest chain, 2026-10-11/12)

| Note | Scripts | Status |
|---|---|---|
| [kahale-image-difficulty.md](../../docs/kahale-image-difficulty.md) | `S:kahale_image_difficulty.py` | rejected, LB-29 |
| [kahale-joint-polarity.md](../../docs/kahale-joint-polarity.md) | `S:kahale_joint_polarity.py` | parked, LB-30 |
| [kahale-witness-charge.md](../../docs/kahale-witness-charge.md) | `S:kahale_witness_charge.py` | parked, LB-30 → LB-08 |
| [kahale-signed-charge-screen.md](../../docs/kahale-signed-charge-screen.md) | `S:kahale_signed_charge_screen.py`, `S:kahale_signed_charge_check.py` | parked, LB-08 (central band rejected) |
| [kahale-preimage-capacity.md](../../docs/kahale-preimage-capacity.md) | `S:kahale_preimage_capacity.py` | rejected, LB-31 |
| [kahale-capacity-lift.md](../../docs/kahale-capacity-lift.md) | `S:kahale_capacity_lift.py` | rejected, LB-31 |
| [kahale-singleton-correction.md](../../docs/kahale-singleton-correction.md) | `S:kahale_singleton_correction.py` | rejected, LB-31 |
| [kahale-pair-correction.md](../../docs/kahale-pair-correction.md) | `S:kahale_pair_correction.py` | rejected, LB-31 |
| [kahale-pair-constraint-generation.md](../../docs/kahale-pair-constraint-generation.md) | `S:kahale_pair_constraint_generation.py` (needs the `kahale_pair_correction.py` base first) | rejected, LB-31 |
| [kahale-low-rank-barrier.md](../../docs/kahale-low-rank-barrier.md) | `S:kahale_low_rank_barrier.py` | rejected, LB-31 (latest note) |

## Coupled faces

| Note | Scripts / Lean | Status |
|---|---|---|
| [kahale-coupled-faces.md](../../docs/kahale-coupled-faces.md) | `S:kahale_coupled_faces.py`, `S:kahale_face_matrix.py`, `L:CoupledFaces`, `L:FaceSortingCriterion` | parked, LB-32 |
| [kahale-face-transport.md](../../docs/kahale-face-transport.md) | `S:kahale_face_transport.py`, `S:kahale_face_relaxation.py`, `L:FaceTransport` | parked, LB-32 |

Every script in `lower-bound/experiments/scripts/` appears above. Run the scripts from the repository root; see
[`../experiments/scripts/README.md`](../experiments/scripts/README.md).
