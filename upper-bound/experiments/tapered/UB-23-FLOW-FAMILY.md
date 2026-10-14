# UB-23 flow-family checkpoint

Status: partial, Lean-checked local interfaces. This is not a global
integer schedule and does not improve the accepted coefficient 1419.

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
  scale condition is `C/256 ≤ B`; this is the schedule-side gate to discharge
  on every lower-expansion phase. It gives each child's reservoir at least
  `1/65536` of its reference scale, while the debt correction is about
  `1/2^24`;
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

These are local contracts: their count, debt, and routing premises are not
derived from one address-indexed placement. The module does not yet prove the
six-stage parity cycle, coverage/disjointness of its register partition, or
the actual transition count equations. `GlobalFlowStep` therefore remains
unrepaired and cannot be applied to frontier addresses just by importing this
file.

In particular, the six-stage proof must establish `C/256 ≤ B` on each lower
expansion phase. Bottom contraction needs a joint integer allocation/receiver
bound. Summing 64 independent child discrepancies is too expensive; the exact
rational identity alone does not provide the cancellation. Bootstrap,
bottom-contraction, and meeting shapes still need to be tied to their actual
integer executions. No
rank-profile recurrence, terminal purity result, or sub-1000 theorem follows.

## Check performed

The focused Lean invocation for `FrontierFlowFamily.lean` succeeded under the
tapered worktree's existing Lean 4.29.0-rc4 environment. It was compiled to a
local helper output under ignored `LLM-helpers/tapered-check`. No package-wide
build or headline theorem/axiom guard was run.
