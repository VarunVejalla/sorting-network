# Pair preimage corrections: finite feasibility and a scale test

## Results (2026-10-11)

A correction depending on singleton **and pair** preimage masses can repair
the ten-term witness charge on every four- and five-wire prefix. A quadratic
polynomial correction suffices, with exact rational verification. However,
that fitted polynomial fails on an actual six-wire prefix. This is progress
in identifying the necessary state, not a universal depth improvement.

Code: [pair correction](../lower-bound/experiments/scripts/kahale_pair_correction.py).
Data: [coefficients and results](kahale-pair-correction-results.json).

## State and endpoint conditions

For four wires, use the complete output image. For five wires, fix output
wire 0 to zero and project the remaining four wires. Let `c_y` count original
input subsets of size one or two whose output lies in the fiber and has
projected mask `y`. There are ten coordinates, in mask order
`1,2,3,4,5,6,8,9,10,12`.

The tested potential is `Phi(R)+h(c)`, where `Phi` is the existing ten-term
charge. The same function `h` is used in both models. Require `h=0` on the
initial profile and every reachable profile with sorted fiber. Therefore
the finite corrected potential still begins at 3 and ends at zero.

The state enumeration retains the labeled outputs of every singleton and
pair input, alongside the entire Boolean image. This makes every layer
transition deterministic and preserves actual-prefix reachability. The
correction uses only the resulting mass histogram, a coarser summary.

## Exhaustive finite checks

| Inputs | Reachable retained states | Parallel transitions |
| --- | ---: | ---: |
| 4 | 201 | 1809 |
| 5 | 11793 | 294825 |

There are 694 distinct correction profiles and 6371 distinct inequalities.
An arbitrary correction table is feasible. More substantially, a polynomial
of degree at most two in the ten mass coordinates is feasible. The script
reconstructs its active linear equations over the rationals and verifies
every inequality and all endpoint equalities exactly.

A linear polynomial was reported infeasible by HiGHS. No exact dual
certificate was extracted for that negative result, so it remains a
numerical feasibility-screen result.

## Six-wire extrapolation fails

For six inputs, fix the first two outputs to zero and project the last four.
Use the same ten mass coordinates and the same fitted polynomial.
In 3200 seeded random actual-prefix transitions, a counterexample appears
after just one prefix layer:

- Prefix: `(0,1),(3,5)`.
- Next layer: `(0,5),(1,3)`.

The corrected potential's drop is approximately 2.1281, exceeding 1.
The stored rational drop is checked by direct evaluation of all 64 inputs.
The sample is not exhaustive. This refutes this particular fitted polynomial,
not every quadratic correction and not every pair-based potential.

## Next obligation

**Update:** [larger-source constraint generation](kahale-pair-constraint-generation.md)
produces an exact six-wire barrier for the entire quadratic correction family,
including a constant term, even when only globally sorted endpoints are fixed.
An arbitrary pair-mass correction table remains feasible on the same sample.

Add actual larger-prefix violations to the polynomial feasibility problem
and refit, testing whether the quadratic family survives as source budgets
grow. A credible candidate must also satisfy sorted-endpoint constraints
at those larger budgets. This is a constraint-generation experiment, not
evidence for an asymptotic coefficient until a general layer inequality
and an across-scale overlap bound are proved.

No Lean work was done. The universal verified coefficient remains
approximately 3.270559454.
