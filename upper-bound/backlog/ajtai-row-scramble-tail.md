# Parked: AKS row-scramble exceptional-column tail

Status: parked 2026-10-10 in favor of the direct multiway partitioner search.
The local two-round screens at `(256,16,256,.55)` and
`(1024,32,1024,.45)` remain valid diagnostics, but they do not give a global
sorting improvement.

The attempted route was to control the number of output columns spilling by
one or more bin widths, then repair those exceptional columns. The audit in
[`SPILL-TAIL-RESEARCH.md`](../experiments/ajtai-multiway/SPILL-TAIL-RESEARCH.md)
found:

* the weak-composition union bound is far too large for an `O(p)` tail at
  width `k/p`;
* the paper's filled-bottom equivalence representative raises average height
  to at most `3*mu/2+k/4`, so its concentration gap vanishes at the middle cut
  for most ranks;
* filling only cells that contribute to a chosen exceptional set makes the
  representative depend on the random row permutations;
* even a true `O(p)` tail is not a repair theorem: the network needs an
  oblivious way to identify, route, and reintegrate the exceptions while
  preserving all cut/fringe guarantees.

The next useful result on this branch would be a uniform discrepancy theorem
over all monotone column-height profiles and selected output sets, or an
oblivious repair construction with a priced all-cuts interface. Without one
of these, do not spend more effort polishing the aggregate leakage constant.
