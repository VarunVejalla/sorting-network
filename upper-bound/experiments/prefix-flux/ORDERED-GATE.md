# The next global test must use the actual wire order

2026-10-20. Codex (GPT-6), fresh-context audit by
`/root/ideal_layout_review`. No new layout theorem is claimed.

Source inspection: `best/AKS/Sub800/R1Wire.lean` defines each bag's wire set
using `rankIn` in the static global wire order. `R1Exec.stageNet` embeds local
comparators with `orderEmbOfFin`. Incoming ports are therefore interleaved by
their static wire labels, not concatenated in source-loop order.

The existing oracle's `--monotone` mode preserves prefixes in its declared
concatenation layout. That layout is a valid abstract routing choice, but it
is not a faithful model of the current implementation's stronger ordered
reachability. All negative traces retain their stated scope: conservation
and coarse count postconditions alone are insufficient. They do not reject
the existing ordered provider or every stronger reachable-state invariant.

Every ascending comparator fixes the ideal Boolean threshold word and is
Hamming nonexpansive relative to it. If the static labels of a bag are sorted
increasingly, its ideal local word is sorted. Consequently global Hamming
error to the threshold word cannot increase. Likewise each global prefix's
zero count cannot decrease. These are general comparator facts, already
compatible with the existing implementation, not a new sorting construction.

In particular, an exact initial-root diagnostic must leave zero errors for
all later stages in this ordered model. Any simulated failure after a fully
sorted root signals a model/layout mismatch. It remains possible for the
count-only relaxation to fail; that does not override this check.

## Bounded implementation target

Keep the new local tail lemma, but test the global recurrence on static
labeled intervals. Initially a bag contains labels [0,N). Each output port
gets a local-rank subinterval of its source's ordered label set. At a receiver,
union the incoming labeled intervals and sort by label. Carry the actual
Boolean color on each interval. A chosen port count can still be represented
by its sorted zero/one split, without allocating N bits. This is a stronger
oracle relaxation, not a fixed universal bounded-depth provider.

Checks: labels partition [0,N); bag cardinalities match D2; prefixes refer
to this actual incoming order; global threshold Hamming error never increases;
an exact root yields no later error; final D2 wire sets have the required
native intervals (a separate geometry obligation).

For the real experiment, the initial root needs a very precise constant-depth
provider, not an exact sort of N wires. Root precision may have arbitrary
fixed cost in the additive constant; ordinary stages must retain their
leading budget. Track the resulting errors against shrinking future subtree
escape capacity, and derive contraction/localization rather than relying
only on a total initial epsilon*N error budget.

`capacity_probe.py --ordered` now implements the static-label test above.
Default mode retains the historical concatenation model. It adds the interval-checked moderate tail and reviewed4r bulk
surcharge, retains the OLD UNPRICED rare-fringe assumption, and uses an
uncertified rectangular bulk scalar. At d16,horizon6,C2^21,epsB.0095 with
exact initial root it still finds an excess of73688 across subtree(2,4).
This rejects that stronger concatenation postcondition model, not the ordered
candidate. Do not mistake it for a new obstruction to the actual layout.

Ordered mode also splits output atoms at the ideal threshold cut, allowing
errors inside a port that crosses q. Policy `global` maximizes current Hamming
error and uses a second LP to prefer native outliers at the same primary
integer objective. Solver optimality is numerical; feasibility and the
integer primary equality are checked. Atomwise internal sorting still
restricts future adversaries. Passing samples are not a universal bound.

Fresh code review passed10495 small label-slicing/error checks and49 small
LP-objective checks against exhaustive enumeration. Recorded controls:

- d16,horizon6,exact root: zero errors and no nonideal choices.
- d20,horizon12,root eps=10^-7:109950 initial global errors, no increase;
  the sampled greedy policy eliminates them at step9, with no capacity gap.
- d16,horizon6,ordinary epsB.0095 also at root: a large capacity violation.

The last control confirms the need for separate root precision. The samples
retain the old UNPRICED epsF1/16,deltaF1/8 assumption; do not combine their
success with the much weaker supported range in TINY-FRINGE as if the same
provider had been tested. The bulk scalar must be an all-wire-cut bound,
including any interpolation surcharge at the added ideal threshold cut.

No Lean until this ordered recurrence, a common priced tiny-rank provider,
root initialization, terminal purity and complete depth accounting pass review.
