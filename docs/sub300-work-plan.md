# Sub-300 work plan

## Objective

Prove

```text
limsup D(n) / log₂(n) < 300,
```

where `D(n)` is the minimum depth of a binary-comparator sorting network.
The accepted repository bound is still 789.75. The D2 route below is a
research candidate, not an established improvement.

## Start here

1. Read [`AGENTS.md`](../AGENTS.md) and [`docs/research-index.md`](research-index.md)
   for repository rules and current project context.
2. Read the [prefix-flux README](../upper-bound/experiments/prefix-flux/README.md)
   for the source map, then its [current handoff](../upper-bound/experiments/prefix-flux/HANDOFF.md)
   for the mathematical status and next gate.
3. Treat `STATUS-HISTORY.md` and `docs/sub300-search.md` as historical search
   logs; prefer the handoff and current gate notes when they disagree.
4. For a compact goal to reuse after context resets, see
   [`sub300-goal.md`](sub300-goal.md) and its [agent guide](sub300-agent-guide.md).

## Current assessment and priority

The accepted upper bound remains `789.75`. The recent D2 work closes several
conditional Lean interfaces, but it does not establish the needed all-stage
physical profile transition or a sub-300 theorem.

The D2 three-sort `(3,3,2)` stage is parked as a proof route. The tile-scatter
variant is not a sorting stage; the sender-wide variant needs a worst-case bulk
leak bound and capture estimate that the current certificates do not provide.
Nearby `Par` geometries do not repair the fringe budget under the audited
schedule. See sections 1 and 7–12 of
[`D2-SPATIAL-INVARIANT.md`](../upper-bound/experiments/prefix-flux/D2-SPATIAL-INVARIANT.md).
These are obstructions to this stage/proof package, not an impossibility result
for sorting networks or for every D2-derived construction.

The exact block-64 rational PSD certificate rules out the standard all-real-space
quadratic-majorant method: on a covered critical rectangle its lower bound is at
least 14.498854 rows. Outside that rectangle, scalar terms already exceed 12.
The degree-two cube-constrained follow-up is also numerically unfavorable
(15.15 rows in an optimistic relaxation); see `prefix-flux/D2-CUBE-SOS.md`.
Higher-degree SOS, other non-union methods, and the sender-wide network itself
remain open.
Do not continue the old tile-to-flow Lean bridge for this stage. The next
research step should compare two routes before adding more formalization:

1. **Try one bounded rescue of sender-wide D2.** Seek a direct, non-union bound
   on the *joint* two-round worst-case leak (or a stronger capture theorem).
   State a quantitative pass threshold using the exact closure script first;
   the current analysis puts the required bulk scale near 12 rows. If no
   plausible inequality improves on the union estimate, leave this stage parked.
2. **Search for a different stage and schedule.** Start from a complete
   profile/impurity recurrence with initialization and terminal cleanup, then
   price every serial layer. The existing direct-multiway profile result alone
   leaves the coefficient at 1419; a new construction must materially reduce
   separator work or change growth per round. Use
   [`direct-multiway/RECURRENCE-BUDGET.md`](../upper-bound/experiments/direct-multiway/RECURRENCE-BUDGET.md)
   as a contract checklist, not as evidence that such a stage exists.

The current D2 gate results, scripts, assumptions, and limits are in the
prefix-flux handoff and `D2-SPATIAL-INVARIANT.md`. Re-read those before choosing
a branch. The best proved coefficient is still `789.75`; there is not yet a
credible, priced route below 300.
## Working rules

- Work only in `.claude/worktrees/sub300` on `sub300-structural`; do not edit the
  main checkout or another worker's worktree. Do not push or promote without
  explicit instruction.
- Before a significant new proof or experiment, state its exact claim, inputs,
  quantifiers, and what outcome would pass or reject the gate. Prefer small,
  decisive structural tests over broad exploratory sweeps.
- Resume by reading the current
  [prefix-flux handoff](../upper-bound/experiments/prefix-flux/HANDOFF.md),
  then inspect only the source files named for the current gate. Keep the
  handoff and experiment index aligned when the recommended next step changes.
- Keep claims labeled as conjecture, simulation/model, hand argument, or
  kernel-checked. A Lean file or finite audit does not by itself establish the
  global recurrence.
- For Lean work, keep scratch modules in the experiment area, use focused
  checks, inspect only relevant errors, and do not introduce `sorry`, axioms,
  `native_decide`, or trust extensions. Follow `AGENTS.md` for final proof and
  contribution checks.
- Commit coherent milestones and handoffs. Keep generated build products and
  run logs out of Git; use the ignored cache and manifest described in the
  prefix-flux README. Keep scripts and source inputs needed to reproduce a
  result with their experiment.
- Update `HANDOFF.md`, `upper-bound/experiments/INDEX.md`, and the relevant
  experiment index when a result changes the recommended route. Mark
  superseded outputs clearly. Avoid duplicating long chronological notes.
- At each checkpoint, report the best supported coefficient, claim level, the
  exact gate closed or failed, what was checked, remaining blockers, and the
  next smallest decisive step. Do not claim success until the complete
  all-input-size theorem is kernel-checked and accepted by the repository's
  contribution workflow.
