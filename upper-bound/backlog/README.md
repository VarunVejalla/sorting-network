# Upper-bound research backlog

This is the ticket index for research ideas that are not part of the current best proof.

**Current endpoint.** `limsup D(n)/log_2 n <= 789.75`, kernel-checked: UB-31, promoted 2026-10-19,
see [`../best/README.md`](../best/README.md). The Lean layer is generic in the invariant scalars, the
separator row window and the fringe classes (`R1Scal`, `R1Point`). The 789.75 point is
`AKS/Sub800/R1At78975.lean`. The previous endpoint, 1419, has its own
[cost audit](../../docs/upper-bound-1419-cost-audit.md).

Tickets record targets and evidence, not results. A projected coefficient is conditional on the
listed construction and proof obligations. The machine-readable source is
[`tickets.json`](tickets.json) (`python3 scripts/tickets --table`; schema in
[`tickets.schema.md`](tickets.schema.md)).

## Below 500: the current program

Plan and cost model: [`sub500-routes.md`](sub500-routes.md). The coefficient is
`(sorts per stage) · S(q) · (stages per bit) = 3 · S(26) · 3/4`. The row exponent `q = 26` comes from two
places:
* the fringe floor `x+y+z + log₂(2(f+1))`;
* the bulk floor (walk bound at `ε_B ≈ 2.55μ − r*`).

Screen (UB-37, model): [`../experiments/sub500-screen/SCREEN.md`](../experiments/sub500-screen/SCREEN.md).
The accepted point sits where the bulk and fringe floors coincide, so a route below 500 has to change at least
two things.

| ID | Priority | Idea | Status | Modelled effect |
|---|---|---|---|---|
| UB-32 | P1 | Two column sorts per stage (short repair instead of the third sort) | proposed | the key lever: 526.5 alone; in nearly every route below 500 |
| UB-34 | P1 | Better fringe scaling: smaller certified `f` at the same `J` | proposed | with UB-32, 2.4x gives 487.5 (q = 25, schedule unchanged) |
| UB-39 | P1 | Merge instead of the first column sort (node input is sorted segments) | proposed | 618.7 alone (idealized) |
| UB-33 | P1 | Remove the residual `r*` (two-sided invariant); `δ_F` is not a lever at (4,5,3) | proposed | 630 alone, 400 with UB-32 and `f/10` |
| UB-40 | P2 | Error-tolerant or periodically restored invariant | proposed | the only modelled route below 300 (tolerance >= 36x, no fringe floor) |
| UB-35 | P1 | Generic failure budgets and root separator in Lean | ready | infrastructure |
| UB-36 | P2 | Generic schedule `(x, y, z)` with per-point design-P checks | proposed | needed once the optimum leaves (4,5,3) |
| UB-38 | P2 | Run-aware first sort and stage fusion at the R1 node | proposed | add-on (<= ~42) |
| UB-37 | P1 | Re-price sweep and structural screen | done (model) | see SCREEN.md |

Gates: three sorts need `q ≤ 20` (472.5); two sorts need `q ≤ 25` (487.5). Recommended first: the UB-32 audit and UB-34 (together the cheapest package below 500).

## Other open tickets

| ID | Priority | Idea | Status |
|---|---|---|---|
| UB-01 | P1 | Local column-sorter interface and its reusable laws | ready |
| UB-02 | P1 | Shallower full sorter at column height `2^26` (below `S(26) = 351`) | proposed |
| UB-04 | P2 | Partial sorting / halving primitives instead of full column sorts | proposed |
| UB-06 | P2 | Expander/halver primitives under a changed composition contract | proposed |
| UB-15 | P1 | Lower fringe floor (smaller `f`); feeds UB-33/UB-34 | proposed |
| UB-11 | P1 | Cumulative boundary displacement in the profile scheduler | active (another agent) |
| UB-19 | P2 | Signed cumulative cut discrepancy in the multiway transfer | proposed |
| UB-24 | P1 | Signed native-prefix rank profile, the two-sided invariant behind route R2 and UB-33 | active (`tapered-945`) |
| UB-26 | P2 | Power-scale localization through recursive overlapping cleanup | active (`ub-26-localization`) |
| UB-18 | P1 | Minimal tapered cut/rank provider contract | ready |

### Below 200 (different architecture)

| ID | Priority | Idea | Status |
|---|---|---|---|
| UB-08 | P3 | Compile the 2024 shallow high-arity k-sorters into binary sorters | parked |
| UB-09 | P2 | Screen feasible finite M before extracting the M-sorter constant | proposed |
| UB-10 | P3 | Recover the reported private sub-100 AKS construction | proposed |
| UB-25 | P2 | Persistent sorted packets with merge-and-deal balancing | proposed |
| UB-27 | P2 | Periodic precision restoration | proposed |
| UB-28 | P3 | Certify a whole randomized multiscale network by paired Boolean witnesses | proposed |

Notes: [high-upside architecture](high-upside-architecture.md) (UB-08 to UB-11),
[sub-200 structural strategies](sub200-structural-strategies.md) (UB-25 to UB-28),
[2024 k-sorting screen](../experiments/k-sorting-2024/README.md).

## Independent sub300 work

- **UB-41**, active on `sub300-structural`: persistent sorted columns with
  incoming redistribution as mixing. Prove a uniform promised-input column
  recurrence and rare-fringe contract before Lean; see
  [the plan](../experiments/persistent-columns/PLAN.md).

## Parked or superseded

- **Superseded by the 789.75 endpoint:**
  - UB-03: rows `< 2^26` were reached by UB-29/UB-31;
  - UB-05: replaced by UB-37;
  - UB-12: replaced by design P;
  - UB-14: rebased into UB-32;
  - UB-07, UB-22, UB-30: the tapered route at 945 / 792 now lies above the accepted coefficient.
- **Parked:** UB-13 (run-aware sort, rebased into UB-38) and UB-20 (adjacent-region compaction).
- [AKS row-scramble tail/repair audit](ajtai-row-scramble-tail.md): equivalence-class rank inflation
  blocks a direct sparse-tail transfer.
- [Archive](archive/README.md): notes calibrated to 1770/1419 or to the tapered route.

## Done

UB-00 (certificate API), UB-16 (contribution pipeline hardening), UB-17 and UB-21 (audits),
UB-23 (tapered per-frontier flow), UB-29 (walk-bound bulk, kernel-checked), UB-31 (789.75).

## Conventions

- **P1** is a direct route to a lower coefficient with the current architecture. **P2** is an
  architectural change with unresolved composition work. **P3** is high-upside exploratory research.
- The status values describe workflow only, not theorem status.
- Promote a ticket to the best package only after its local guarantees, global schedule, depth
  theorem, focused build, full build, and headline/axiom guards are checked as appropriate.
- Negative results go to [ruled-out.md](ruled-out.md). Recheck any item there whose assumptions
  changed, for example under the walk bound.
