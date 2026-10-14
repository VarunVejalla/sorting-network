# UB-23 flow-family checkpoint

Status: partial, Lean-checked local interfaces. The lower-expansion scale gate
is now derived from the candidate schedule, and the corresponding integerizer
has a schedule-specific wrapper. This is not yet the global integer schedule
and does not improve the accepted coefficient 1419.

## Implemented

`FrontierFlowFamily.lean` now indexes counts by bootstrap, ordinary interior,
top advance, top retreat, bottom expansion, bottom contraction, and meeting
shapes. Advance/retreat and expansion/contraction have distinct tags even
when they share the same rational mass target.

The file provides:

* the existing ordinary `LocalIntegerFlow` behind an interior-shaped count;
  `scheduled_interior_ports_match` requires the tagged debt to equal the
  actual bag debt;
* typed adapters for top-advance and top-retreat integerizers;
* a new bottom-expansion integer split. It allocates one even interior up-port
  and 64 bottom children, using the bottom frontier's own mass targets. The
  split requires `C/256 ≤ B` and gives each child's reservoir at least
  `1/65536` of its reference scale, while the debt correction is about
  `1/2^24`;
* `FrontierScheduleGate.lean` proves the lower-frontier six-stage cycle,
  derives `3*omega(t) <= t+4` whenever that frontier expands, and converts it
  to the exact rational capacity condition `C/256 <= B`. Its wrapper applies
  the bottom-expansion integerizer with candidate-schedule `B` and `C`, so
  this scale condition is no longer a caller-supplied premise;
* exact rational conservation formulas for top advance/retreat, bottom
  expansion/contraction, and meeting;
* receiver discrepancy lemmas. Top advance costs at most
  `1 + 69/64 + 64 = 66.078125 < 69` wires when each incoming child up-port
  is within one wire. An ordinary interior receiver costs
  `1 + 70/64 + 64 = 66.09375 < 69`; a retreat receiver costs at most 64
  wires under unit rounding on each port;
* the equal-scale meeting identity with an explicit ±138 bound when its two
  frontier count errors are independently bounded by 69.

## Still open

These remain local contracts: their count, debt, and routing premises are not
derived from one address-indexed placement. The new cycle theorem covers the
lower-frontier scalar schedule only; it does not prove the six-stage typed
count/port cycle. Coverage/disjointness of the register partition and actual
transition count equations are still open. `GlobalFlowStep` therefore remains
unrepaired and cannot be applied to frontier addresses just by importing this
file.

The remaining six-stage proof must tie each phase's tagged count and port
allocations to the actual global router. Bottom contraction needs a joint
integer allocation/receiver bound. Summing 64 independent child discrepancies is too expensive; the exact
rational identity alone does not provide the cancellation. Bootstrap,
bottom-contraction, and meeting shapes still need to be tied to their actual
integer executions. No
rank-profile recurrence, terminal purity result, or sub-1000 theorem follows.

## Check performed

Focused Lean invocations for `FrontierFlowFamily.lean` and
`FrontierScheduleGate.lean` succeeded under the tapered worktree's existing
Lean 4.29.0-rc4 environment. The latter proves the scalar cycle, schedule
scale gate, and wrapped expansion split. Outputs are local helper artifacts
under ignored `LLM-helpers/tapered-check`. No package-wide build or headline
theorem/axiom guard was run.
