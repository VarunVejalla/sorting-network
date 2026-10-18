# A five-wire obstruction to the conditional-fiber lift

## Exact actual-network counterexample (2026-10-11)

The four-wire witness charge does not retain unit layer drop when applied
to a four-wire output fiber of a larger network. This obstruction uses an
actual comparator prefix, rather than an abstract feasible domain.

Use zero-based wire indices. On five inputs, take the prefix

1. `(0,1),(2,3)`;
2. `(0,2)`.

Fix output wire 0 to zero and project onto wires 1 through 4. The resulting
four-wire domain is

`{0,1,3,4,5,6,7,8,9,11,12,13,14,15}`.

It contains every four-wire sorted point. Append `(1,3),(2,4)` on the global
network, equivalently `(0,2),(1,3)` on the projection. The ten-term potential
falls from **3 to 1**, violating a unit-drop bound.

The [script](../lower-bound/experiments/scripts/kahale_capacity_lift.py)
checks all 32 inputs, the concrete fiber map's weight preservation and
monotonicity, and all 32 rank-two output-edge Hall subsets.
[Exact data](kahale-capacity-lift-results.json) includes both images.
No Lean formalization was attempted.

## Why the four-wire capacity proof does not apply

The prefix's first output is the AND of the first four inputs. Therefore the
preimage of this output-zero fiber is the 30-point lower ideal

`{S subset {0,1,2,3,4} : {0,1,2,3} is not contained in S}`.

In particular, **all five singleton inputs survive**. Their projected output
routes are `(0,0,2,2,3)`, giving multiplicities `(2,0,2,1)`, whose sum is 5.
They satisfy both the general rank-two Hall inequality and all individual
rank-three demands. The fiber map is genuinely monotone and conserving on
its input lower ideal, but its domain is not a four-dimensional input cube.

Thus full consistency does not repair this lift. The missing hypothesis is
the four-source budget. Conditional output fibers can retain more input
sources than output wires. The earlier four-wire result remains valid.

## Consequence for the research target

**Follow-up:** [singleton-only corrections fail](kahale-singleton-correction.md)
even without endpoint constraints. An actual next comparator leaves every
singleton route unchanged while producing a potential drop of `5/3`.
Pair or higher-rank preimage information is therefore needed to repair this
particular charge.

Do not apply the ten-term charge unweighted to conditional four-wire fibers.
A scalable candidate must carry input-preimage information as part of its
state and prove a layer inequality for that richer state.

Here the next layer merges singleton groups of sizes 2 and 2. The collision
count `sum_i binom(m_i,2)` rises from 2 to 6. This identifies the capacity
consumed by the extra potential drop. However, adding a positive collision
correction does not immediately give a depth bound: sorting merges all
singleton routes, so that correction is also large at the terminal state.
Its endpoint cost and preparation cost must be included in any amortized
argument.

The next feasibility target is a preimage-aware joint charge whose terminal
value vanishes, tested on these actual fibers before an across-scale sum.
The universal checked coefficient remains approximately 3.270559454.
