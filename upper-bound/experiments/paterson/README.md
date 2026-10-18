# Paterson requirements versus cost experiment

This experiment audits the completed rounded Paterson construction, separately
from `upper-bound/best` and the archived working implementation.

- [Requirements and cost](requirements-versus-cost.md): contracts actually consumed by the proof, and what a replacement must provide.
- [Conditional global bound](conditional-bound.md): scheduler accounting, dependence on errors, and numerical targets.
- [Root-repair interface](root-repair-interface.md): minimal consumed postconditions and a relaxed bin contract.
- [Hierarchical partitioning](hierarchical-partitioning.md): four-level construction, cumulative error budgets, and the exact-first-split obstacle.
- [Concentration and exact repair](concentration-and-repair.md): recursive exact capture, fixed-pool repair, and the current cost obstruction.
- [Concentration accounting](concentration_budget.py): scalar recursive core-size/depth experiment.
- [Sparse concentration and pool selection](sparse-concentration-and-pool-selection.md): cheaper support-adaptive halvers, one-layer layout, and an uncertified 406-layer first-split candidate.
- [Sparse-halver accounting](sparse_halver_budget.py): numerical candidate exploration; entropy ceilings are not formal certificates.
- [Uniform bound and suffix audit](uniform-bound-and-suffix.md): rational-certified scalar envelope gives a conditional 444-layer first split; no cheap complete suffix is established.
- [Uniform concentration certificates](uniform_concentration.py): covers all sizes up to the root-window bag maxima with exact rational log intervals.
- [Joint bin/pool allocation](joint-bin-pool-allocation.md): signed-prefix transfer formula, spillover example, and the cost of a sufficient purity construction.
- [Joint allocation accounting](joint_pool_allocation.py): exact example and conservative full-purity cost envelope.
- [Balanced signed-prefix target](balanced-signed-prefix.md): protected-set invariance, residual slack, and a conditional native-reservoir probe window.
- [Signed-prefix scalar budgets](signed_prefix_budget.py): sufficient contraction/slack arithmetic.
- [Native reservoir supply and exchange depth](native-reservoir-exchange.md): allocation supply fails the current window certificate; conditional graph exchange lemma and direct coverage accounting.
- [Reservoir arithmetic](reservoir_budget.py): exact endpoint calculations and directional dyadic prefix bounds.
- [Global circulation and invariant slack](global-circulation-and-slack.md): direct-exchange obstruction, joint resource counts, and the limited slack in current parameters.
- [Circulation/slack arithmetic](circulation_slack_budget.py): exact error-scale and protected-capacity diagnostics.
- [Paired boundary cores](paired-boundary-cores.md): exact two-block residual/imbalance identity, monotone crossing potential, and composition obligations.
- [Paired-core budgets](paired_core_budget.py): conditional uniform pair depths.
- [Aggregate ancestor scheduler](aggregate-ancestor-scheduler.md): contraction above the imbalance floor and necessary local-support guards.
- [Aggregate scalar constraints](aggregate_scheduler_budget.py): exact fringe-capacity and pair-contraction calculations.
- [Four-block hybrid epoch](four-block-hybrid-epoch.md): conditional `5 epsilon` contraction, aggregate-derived local guard, and the asymmetric primitive gap.
- [Four-block count exploration](four_block_epoch.py): exhaustive finite oracle exploration; no comparator network is constructed.
- [Concrete extreme cores and forecast](extreme-core-construction-and-forecast.md): supported halver cascades, certified scalar costs, and why the current route does not forecast an improvement over 1770.
- [Extreme-core cost certificates](extreme_core_cost.py): rational-certified stage depths and global accounting numbers.
- [Exact arithmetic script](audit_budget.py): run with `python upper-bound/experiments/paterson/audit_budget.py` from the repository root.

Status (2026-10-10): the existing sorting theorem is kernel checked in the
legacy package. The conditional derivation here is an informal mathematical
audit of its recursion, with exact rational arithmetic checked by Python.
There is no new sorter or improved sorting theorem in this experiment.
No production proof files were changed, and no Lean build was run for this audit.
