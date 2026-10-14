# Coupled multiway recurrence audit

Status: research note / hand derivation, not a sorting bound. Written on the
UB-26 worktree as a reusable cross-workstream handoff. Inputs are the current
`upper-bound/best/AKS/Chvatal/Schedule7.lean` and `StageKernel.lean`, plus the
active direct-multiway profile files in the main checkout. No Lean theorem was
added or checked here.

Read [`COUPLED-RECURRENCE.md`](COUPLED-RECURRENCE.md) for the weighted active-
level error sum and its limits. Read [`TAPERED-HANDOFF.md`](TAPERED-HANDOFF.md)
for the status of the conditional 528 model and the other tapered estimates.
Read [`STAGE-ARCHITECTURE-SCREEN.md`](STAGE-ARCHITECTURE-SCREEN.md) for the
below-200 stage budgets and the recommended 32-way spill-tail gate.

The next proof gate is to formalize the active-level geometric sum and the
boundary-displacement aggregate inequality, then instantiate the exact
stage-to-stage map for all rank channels. The formulas below are candidate
interfaces, not currently proved global recurrences.
