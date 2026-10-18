# UB-23: initialized frontier flow schedule

Status: UB-23 complete at the kernel-checked count/ownership level. A fresh
source rebuild of all 32 local modules and four endpoint axiom guards passed
on 2026-10-14 with Lean 4.29.0-rc4. The accepted sorting-depth coefficient
remains 1419.

## Endpoint

`FrontierIntegerSchedule.lean` constructs `candidateIntegerSchedule d hd` for
all `d >= 14`. It is one actual `RaggedWirePartition` at every time, initialized
at the raw root, routed through the static-debt bootstrap, and continued to
`candidateTerminalCutoff d = 3*d - 23`.

The principal theorems are:

- `candidate_integer_schedule_invariant`: at every stage from 1 through the
  cutoff, actual register counts are even, inactive registers are empty, and
  each active register is within 69 wires of its own shape's mass target.
- `candidate_integer_schedule_routed`: every transition before the cutoff,
  including the initial root route, has one coherent address-indexed even-port
  table that realizes the next ownership partition through the physical tree
  router.
- `candidate_six_stage_integer_cycle`: every valid six-stage segment has all
  seven count invariants and actual split tables for all six transitions.
- `candidate_integer_terminal_counts`: only level `d-7` is occupied at the
  terminal meeting, every register is even, and its count is within 69 of
  the native target `64^7`.

There are no extra frontier-discrepancy, parity, bootstrap-count, or cohort
history premises on these endpoints. The history needed for a contraction is
created by preceding expansion steps inside the schedule induction.

## Construction

`FrontierEvenFlow.lean` gives each flow shape its own port targets and uses a
shared even integerizer. Up-ports round within one wire; down blocks are even
and round within `2 + 70/64`. Every register receives only even contributions.

`FrontierFlowTable.lean` chooses a source's split once at its actual register
cardinality. `FrontierFlowSupport.lean` proves its nonempty ports land in the
next active parity band. `FrontierRootRoute.lean` handles the clipped root.
`FrontierRoutedReceivers.lean` proves the regular, upper-retreat and new-bottom
receiver counts for this same table.

`FrontierCountStep.lean` carries two phase-dependent facts alongside the count
invariant. The second expansion has a fresh bottom source error at most
`2 + 70/64`. At contraction, its emitted children retain their exact cohort
sum, equal to that source's count minus its up-port. Thus contraction and
terminal meeting cost at most `115/16 = 7.1875` wires, rather than the sum of
64 independent register errors. Regular receivers cost at most
`2 + 70/64 + 64 = 67.09375`; upper retreat costs at most 64. All fit within 69.

The terminal count target is the native reservoir `B`: one top-advance down
port plus a whole bottom cohort. The equal-scale auxiliary mass
`(2-1/Q)*C` is not used as the meeting receiver's target. Early bootstrap
frontiers can coincide, so the cutoff is called the terminal meeting, not the
first equality of the two frontier functions.

## Bootstrap change and remaining tickets

The old uniform stage-three reset does not initialize static address debt.
The new schedule instead splits each first-level native register directly
into a top-retreat up-port and static-debt bottom children. Their rational
masses sum exactly to the native input, and the even integerizer preserves
its actual count. The previous bootstrap row provider and reset/rank lemmas
are not used to assert this new initialization.

UB-22 must realize the resulting port profiles by suitable comparator
networks with the advertised depth. UB-24 must prove the rank/native-prefix
invariant and terminal cleanup against this ownership sequence. Existing
bootstrap rank estimates must be adapted to the new allocation. The flow
schedule proves count feasibility and conservation, not sorting correctness
or a sub-1000 bound. `GlobalFlowStep.lean` is the historical conditional
ordinary-only interface; use `FrontierIntegerSchedule.lean` for UB-23.

The subsequent [UB-24 checkpoint](UB-24-RANK-PROFILE.md) proves exact
threshold recurrences on this execution and identifies a stronger retirement
obligation: exact native subtree totals. The local rounding contract above
does not force those totals. This does not invalidate the UB-23 count theorem
or establish that its selected trace is unsortable; a coordinated rounding
refinement or a proof of exact balance is needed for the rank argument.

## Verification

The focused checker `check-flow.ps1` rebuilds the endpoint's local import
graph from the worktree sources in a separate helper directory, then compiles
`FrontierFlowAxioms.lean`. It needs the pinned Lean executable and the existing
best-package build library. Example from the repository/worktree root:

```powershell
& upper-bound/experiments/tapered/check-flow.ps1 `
  -LeanExe 'C:/Users/Varun/.elan/toolchains/leanprover--lean4---v4.29.0-rc4/bin/lean.exe' `
  -BestLib 'C:/Users/Varun/Documents/Projects/Math Research/sorting-network/upper-bound/best/.lake/build/lib/lean'
```

Build outputs, quiet logs and source hashes stay in ignored
`LLM-helpers/ub23-build`.

The guarded schedule, routing, six-stage and terminal-count endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`. All 32 rebuilt source
hashes matched the final worktree. The ticket registry and whitespace checks
were also validated; the registry validator still reports older stale-entry
warnings unrelated to UB-23. No full experiment/package build or sorting-bound
contribution check was run. The worktree changes are not committed or pushed.
