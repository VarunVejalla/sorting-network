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
Read [`FIXED-CORE-TAIL-RECURRENCE.md`](FIXED-CORE-TAIL-RECURRENCE.md) for the
exact layer-cake crossing identities and the rank-profile screen induced by
the available all-cut leakage theorem, plus a seeded 1024-way-core attack
finding 42 one-band spill columns at the middle rank and cut.

The next gate for the high-arity route is a simultaneous upper tail bound for
the actual seeded core over all monotone profiles, ranks, cuts and orientations.
The greedy attack script only finds lower witnesses. Independently, the
active-level sum and boundary-displacement formulas remain hand derivations,
not formalized global recurrences.
