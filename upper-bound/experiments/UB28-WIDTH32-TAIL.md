# UB-28: exact width-32 terminal blocks

Status: promising rate-screen variant; no sorting bound is proved.

## Construction and cost

Sort every fixed block of 32 wires with Batcher's bitonic network
(`bitonicSort 5`, depth bound 15; see
[`AKS/Bitonic/Net.lean`](../best/AKS/Bitonic/Net.lean)). Run the randomized
merge schedule only at dyadic widths `h >= 64`,
with two matching offsets and `d_h` independent uniform matching rounds per
offset. Use a top-relative alternating schedule: `high` rounds at one parity
of scales and `low` at the other. Sorting inside the 32-wire blocks leaves a
bad output only at a boundary between two such blocks; if their one-counts
are `a,b`, that boundary is bad exactly when `a > 0` and `b < 32`.

For `n=2^L`, the depth is

```text
15 + 2 * sum(d_h for h = 2^6, 2^7, ..., 2^(L-1)).
```

Thus `(high,low)=(280,20)` has modeled limsup coefficient 300,
`(260,20)` has coefficient 280, and constant `d_h=70` has coefficient 140.
The exact width-32 tail replaces only a fixed-width stage, so its depth adds
15 rather than a term proportional to `L`.

## Finite lattice screens

`ub28-width32-tail-screen.py` evaluates the annealed max-path recurrence with
a grid of 16 count fractions and binary64 log-binomial coefficients. At
`n=2^24`, it screened 97 block-boundary positions: the first and last 32
boundaries and 33 positions around the center. The `(280,20)` schedule had
minimum `0.722397280754`; `(260,20)` had minimum `0.698156144812`; both minima
were at center boundaries 262142 and 262144.

The best tested schedule is now `(223,27)`, whose modeled coefficient is 250.
Its full 97-position grid-16 screen has minimum rate `0.723364926421` at
center boundaries 262142 and 262144, about `0.03022` above `ln 2`. A hybrid
screen keeping all 33 width-32 counts through the width-64 matching stage,
then restricting to grid 16, gave `0.723364770036` at those same boundaries.
The first finer stage changes the sampled rate by only `1.6e-7` there.

The center rate for `(223,27)` converges numerically across powers of two:

| `log2(n)` | 16 | 20 | 24 | 28 | 32 | 40 | 48 | 64 | 96 | 128 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| grid-16 center rate | 0.679378 | 0.720257 | 0.723365 | 0.723354 | 0.723353 | 0.723353 | 0.723353 | 0.723353 | 0.723353 | 0.723353 |

At exponent 128, the central boundaries two blocks left of center and at
center both give `0.723353354118`. This suggests a stable limiting margin of
about `0.0302`, but the sequence is still a restricted-grid numerical
diagnostic, not a certified rate bound.

Schedule tuning is sensitive to the two parities. At the center, `(212,28)`
and `(214,26)` (coefficient 240) give `0.694176571259` and `0.696956423630`,
while `(215,25)` gives `0.691093414814`. The tested `(223,27)` coefficient-250
point has a more useful margin. Constant 70 rounds per offset, despite its
modeled coefficient 140, has a center path below threshold (`0.358128276908`
at boundary 262128; nearby boundaries are about `0.3578`) and fails this
first-moment screen. `(230,20)` also fails at coefficient 250 (`0.661112522559`
at the center), so simply fixing the sum of the two parities is not enough.

The constant-70 run exposed a center feasible-lattice path with rate
`0.358128276908` at boundary 262128; nearby center boundaries reached
`0.357817616187`. I stopped that sweep after finding this counter-screen.
It shows the grid-16 first-moment gate fails for that schedule at this finite
screen; it does not prove that no sorting network in the ensemble sorts.

These computed rates maximize log-probability only over the selected feasible
count lattice. Restricting the path set can only lower that maximum, so the
reported negative log-cost is an **upper bound** on the unrestricted minimum
cost. Off-lattice paths may have much higher probability and lower cost. The
screens therefore cannot establish the required `I > ln 2`. The 97 positions are
also representatives, not a proof of every size and every boundary phase.
The `(223,27)` margin is the current lead; the `(260,20)` margin is only
`0.005009` and is too thin to prioritize over it.

Reproduce the screens after building the optional native kernel as described
in [`UB28-TOP-HEAVY-SCHEDULE.md`](UB28-TOP-HEAVY-SCHEDULE.md):

```powershell
python upper-bound/experiments/ub28-width32-tail-screen.py --log-n 24 --grid 16 --high 223 --low 27 --native-dll $env:TEMP\ub28_maxplus_kernel.dll
python upper-bound/experiments/ub28-width32-tail-screen.py --log-n 24 --grid 16 --high 223 --low 27 --edge 262142 --edge 262144 --fine-bottom-grid32 --native-dll $env:TEMP\ub28_maxplus_kernel.dll
```

## Proof gate and next technical test

The favorable screen is not the missing proof. A certificate must upper-bound
the maximum log-probability over the *continuous* feasible profile paths,
uniformly over all boundary phases, and bound finite-width binomial and path
counting errors by `o(n)`. The current cell Bellman loses within-cell profile
memory and returns a vacuous rate; merely increasing its flat grid does not
fix that reset.

One finer screen retained all 33 width-32 counts through the first width-64
matching stage, then restricted to the width-16 lattice before the state
expands. At the worst center phase this hybrid changed the `(223,27)` rate by
only `1.6e-7`. Running that finer state over all phases hit
a `33^6` table (about 10.3 GB), so a sparse/structured representation is
needed before broadening the refinement. A support-local pair iterator now
avoids scanning every block at each reverse layer; it agrees exactly with the
previous full scan on 80 randomized cases and exhaustive support-pair tests
through 19 blocks. It lets the grid-16 screen reach `log2(n)=128` quickly.

The new `ub28-width32-phase-audit.py` starts from the two-block boundary
event and closes its interval support through the reverse split and both
matching offsets. It finds 19 initial phases, 41 reachable phases, 91 arcs,
and maximum support length six. This graph is unchanged when its scale horizon
grows from 24 to 128; the representative-position rule also matches
exhaustive edge phases for every block count from 2 through 2048. This is a
finite computational audit, not a proof of phase coverage at all scales, but
it gives the analytic gate a concrete finite state set. The potential must
also remember the alternating schedule parity, giving at most 82
phase/parity states.

The decisive next step remains a continuous Bellman supersolution that
preserves a shared profile across scales, with interval-certified kernels and
uniform finite-width entropy error. The finite graph makes this a targeted
supersolution search over 41 support types, rather than another all-edge
enumeration. No Lean stage bridge should be extended until that analytic gate
is informative.

## Modal off-grid gate (2026-10-25)

The grid-16 upper-cost screen omits many integer counts: at width 32 it only
represents even counts. The actual central-boundary event accepts any counts
`left>0`, `right<32`, and a feasible modal trajectory under the top-relative
`(223,27)` schedule reaches `(29,28)`. The reproducible script
[`ub28-width32-modal-gate.py`](ub28-width32-modal-gate.py) follows that path
from balanced top halves. Runs for every `log2(n)` from 7 through 100 and
additional exponents through 1024 all end at `(29,28)`; this is still a
computational observation, not an all-scale recurrence proof.

Each selected matching outcome is a mode of a hypergeometric law with at most
`h+1` possible outcomes at block width `h`, so its probability is at least
`1/(h+1)`. Each selected split mode has the same lower bound. The path uses at
most a constant number of supported pairs per scale, so this gives a
`exp(-O(log^2 n))` lower bound on its probability, conditional on the balanced
top counts. The balanced input type itself contains at least
`2^n/(n/2+1)^2` inputs. At `n=2^20`, even the deliberately crude modal bound
already gives `log E[failing inputs] > 685,000`; the 250-coefficient random
ensemble therefore fails its first-moment sorting gate at that size. This is
not an impossibility result for deterministic networks, and the all-scale
modal terminal recurrence still needs a proof. It is, however, a concrete
off-grid obstruction to the current continuous-rate screen and makes a
continuous Bellman certificate for this schedule implausible unless it first
resolves this path.
