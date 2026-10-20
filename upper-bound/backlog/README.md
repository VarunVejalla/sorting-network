# Upper-bound research backlog

This is the ticket index for research ideas that are not part of the current best proof.
The current kernel-checked endpoint is `limsup D(n)/log_2 n <= 789.75` (UB-31, promoted 2026-10-19); see
[`../best/README.md`](../best/README.md). The previous endpoint 1419 has its [cost audit](../../docs/upper-bound-1419-cost-audit.md).
Tickets record targets and evidence, not established results. A projected coefficient is conditional
on the listed construction and proof obligations.

The tapered branch's UB-23 count/ownership endpoint is documented in
[`UB-23-FLOW-FAMILY.md`](../experiments/tapered/UB-23-FLOW-FAMILY.md).
It supplies an initialized shape-specific integer schedule. Comparator-network
realization and rank correctness remain separate obligations; the accepted
sorting-depth coefficient is unchanged.

UB-24 is active: [signed rank/retirement checkpoint](../experiments/tapered/UB-24-RANK-PROFILE.md).
Exact prefix recurrences are implemented. Exact subtree balance at retirement
needs a stronger coordinated rounding construction before the global rank
induction can close.

## Active candidates

| ID | Priority | Idea | Status | First deliverable |
|---|---|---|---|---|
| UB-01 | P1 | Abstract the local column-sorter interface and identify the exact reusable laws | ready | Lean interface plus a cost table for replacing bitonic without touching separator mathematics |
| UB-02 | P1 | Search for a shallower full sorter at ordinary-node widths | research | Candidate family with a proved depth below 800 at `m` around `2^42`–`2^43`, or a documented obstruction |
| UB-03 | P1 | Reduce the ordinary-node height using stronger/tighter separator estimates | in progress | Certified parameter window and end-to-end coefficient; two-round Variant B currently projects 1354.5 only |
| UB-04 | P2 | Replace full column sorts with partial sorting / halving primitives | research | State the weaker invariant sufficient for the next separator round and derive a depth budget |
| UB-05 | P2 | Jointly optimize branching factor, number of rounds, and node geometry | research | Small exact/rational parameter sweep with a valid global-schedule cost formula |
| UB-06 | P2 | Improve expander/halver primitives and compose them with the current node contract | research | A concrete halver depth/error pair and a compatible fringe/bulk guarantee |
| UB-07 | P3 | Tapered stranger invariant allowing larger local error | parked | Recalibrated parameter model against the 1419 endpoint, then a target below 1200 |
| UB-08 | P1 | Compile the 2024 shallow high-arity k-sorters into binary sorters | research | An explicit finite arity schedule and a proved binary coefficient below 200, or a quantitative barrier |
| UB-09 | P1 | Extract finite-M constants from Chvatal's M-sorter construction | research | Prove a finite `c_M` at `M=16` or `32` and check `c_M * d₂(M)/log₂ M < 200` |
| UB-10 | P3 | Recover the reported private sub-100 AKS construction | speculative | Locate a public finite-parameter construction or identify the missing theorem/contract |
| UB-11 | P1 | Price cumulative boundary displacement in the profile scheduler | in progress | Prove the aggregate rank-window mismatch bound and recompute the rank-1 transfer coefficient |

## Ticket conventions

- **P1** means a direct route to a lower coefficient with the current architecture.
- **P2** means a potentially substantial architectural change with unresolved composition work.
- **P3** means high-upside exploratory research with significant model or proof uncertainty.
- `ready`, `in progress`, `research`, and `parked` describe workflow only; they do not indicate theorem status.
- Promote a ticket to the best package only after its local guarantees, global schedule, depth theorem,
  focused build, full build, and headline/axiom guards are checked as appropriate.

## Completed infrastructure

- **UB-00 — Global certificate API:** complete. `AKS.Bounds.Certificate` fixes a construction-independent
  interface over the canonical comparator network model and minimum-depth function. The separate
  [`upper-bound/contributions`](../contributions/README.md) package imports that API and includes a
  compiled smoke test. It derives the limsup coefficient from a closed network-family certificate.

## Parked structural branch

- [AKS row-scramble tail/repair audit](ajtai-row-scramble-tail.md): equivalence-class rank inflation blocks a direct sparse-tail transfer; revisit only with a uniform discrepancy theorem or oblivious repair.

## Existing research notes

- [Ordinary-node depth tickets](ordinary-node-tickets.md): scope, target, acceptance test, and dependencies for UB-01 through UB-07.
- [High-upside architecture tickets](high-upside-architecture.md): the 2024 k-sorting lead (UB-08), finite-M Chvatal route (UB-09), and private Komlos report (UB-10).
- [UB-11: cumulative boundary displacement](high-upside-architecture.md#ub-11--price-cumulative-boundary-displacement-in-the-profile-scheduler): the missing rank-1 profile-transfer bound for the active direct-multiway schedule.
- [2024 k-sorting screen](../experiments/k-sorting-2024/README.md): theorem scope, s-sorted invariant, and preliminary binary-depth checks for UB-08.
- [Few-hundred tapered-invariant track](few-hundred-tapered-invariant.md): older parameter-model study, calibrated to the former 1770 endpoint; retained as background for UB-07.
- [Ruled-out and screened ideas](ruled-out.md): prior negative screens. Recheck any item whose assumptions changed under the 1419 two-round proof.
