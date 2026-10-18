# UB-25 terminal-gate paper test

Date: 2026-10-18. Scope: test the proposed fixed-round spectral estimate as a
way to turn moderate packet-profile error into a rare-rank-safe terminal
condition. No routing Lean or scheduler simulation was added.

## Candidate invariant tested

The proposed sufficient local condition is that, for every Boolean threshold,
each packet's count differ from its assigned target count by at most eight
wires. A rank-aligned eight-wire fringe would make a singleton threshold
harmless: one exceptional key can fit inside the fringe. The essential
assumptions are rank alignment and preservation of the eight-wire allowance
through every stage; neither follows from a count bound around the cohort
mean alone.

For a cohort of `c` sorted packets, let `H` be the total threshold count and
`x_j` the count in output packet `j`. The checked 15-round cycle for
`c <= 130` has centered spectral norm `rho <= 1/16`. The rounded merge-and-deal
calculation recorded in `MIXING-TAIL.md` gives

```text
max_j |x_j - H/c| <= rho*H + 15/2 <= H/16 + 7.5.
```

This certifies deviation at most eight only when `H <= 8`. For `H > 8`, the
inequality no longer proves the proposed fringe condition. That is a failure
of this sufficient estimate, not a counterexample to the actual matching
cycle. The exact singleton obstruction is therefore not decisive by itself:
a singleton fits in an eight-wire fringe if its packet has the correct rank
interval. The unproved issue is preservation for larger threshold mass and
the actual interval assignment.

The unbounded global step is weaker for this purpose. A product of `R=9`
pairwise averaging matchings has at most `2^9` nonzero input dependencies in
each output row. For a doubly stochastic `C x C` product `P`, each row has
squared Euclidean norm at least `1/2^9`. Since
`||P-J/C||_F^2 = ||P||_F^2 - 1` and the centered operator has rank at most
`C-1`,

```text
||P-J/C||_2 >= sqrt((C/2^9 - 1)/(C - 1))  (C > 2^9).
```

This lower bound tends to `1/sqrt(512)`. Thus no nine-round matching product
can have a centered spectral norm tending to zero uniformly in `C`. Applying
the available rounded bound `rho*H + 9/2`, even an optimal spectral-norm
certificate cannot guarantee an eight-wire deviation once `H` exceeds about
79 in the large-`C` limit. For threshold masses growing with packet count,
the proposed spectral certificate cannot establish the invariant. A
different, pointwise rank-aware count argument could still succeed.

## Progress rate and repair cost

For the unchanged Chvatal schedule, `N=64^d` has `log2(N)=6d`, while
`ordinaryRounds(d)=3d-21`. Therefore the asymptotic conversion is exactly two
log bits per ordinary round, up to additive root/final terms. The 2-bit
division in the packet cost screens is valid if one packet transition fits
inside each ordinary round and the original schedule remains unchanged. A
redesigned slower flow would need a new rate calculation.

`flowA7` specifies port sizes and routing; port routing is wiring and costs
zero comparator layers. The separate checked
`flowA7_sourcePortRepairStage` has depth at most six per ordinary round when
used. If required on every ordinary round, it adds 3 to the coefficient.
Whether the 78-layer full-block sort subsumes this repair is unresolved
because the physical next-stage rank map is missing. Thus the raw conditional
screens are 195 (or 198 with repair) for the proposed 15+9-round plan, and
240.5 (or 243.5 with repair) for the conservative 15+16-round composition.
All still omit the unresolved output routing and terminal cleanup.

## Exit result

No invariant or cleanup with a proved depth was found that reaches the exact
Boolean terminal criterion. The fixed-round spectral/fringe route is **NO-GO
for the current sub-200 candidate**: it controls only bounded threshold mass,
does not evolve the actual packet rank targets, and the aggregate recurrence
has a nonzero steady-state floor. This does not prove that every packet
algorithm is impossible below 200.

To reopen the route, first provide one of these paper-level results:

1. A rank-aware multiscale count invariant that covers all threshold masses,
is preserved across actual `WireFlow` rank intervals, and reaches an exact
terminal condition; or
2. A depth-costed cleanup network whose hypotheses follow from a uniform
outsider/dirty-interval bound, including rare ranks.

Until then, do not spend more Lean effort on the `nextSlot` plumbing for this
fixed-round candidate. The checked merge machinery may be more productive on
the run-aware sorting route, where sorted-run input is already guaranteed.
