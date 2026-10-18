# High-upside architecture tickets

These tickets preserve global approaches that could substantially beat 1419.
They are research directions, not proved improvements. UB-11 is the immediate
proof obligation for the active direct-multiway weighted-profile route; UB-08
remains the separate 2024-literature lead.

## UB-08 — Compile the 2024 shallow high-arity k-sorters

**Priority:** P1 · **Status:** research · **Focus:** arbitrary-arity recursion and binary compilation.

Dobrokhotova-Maikova, Kozachinskiy, and Podolskii, *Towards Simpler Sorting
Networks and Monotone Circuits for Majority* (APPROX/RANDOM 2024), give a
high-dimensional-cube architecture for k-sorting networks. Their Theorem 2
states depth at most `(2 + o(1)) (log_k n)^2` when
`log k = ω(log log n)`; here a comparator sorts all items in its block of size
at most `k`. This is not a binary sorting-network bound. The paper observes
that a good k-sorting network can be applied recursively to its own
comparators until the arity reaches 2.

The first calculation rules out black-box substitution as an immediate
improvement. If each k-comparator is replaced by a binary sorter of depth
`S(k) <= C log₂ k + O(1)`, the composed depth is at most the k-sorting depth
times `S(k)`. Taking `k = n^α` gives binary slope about `2C/α`, which is at
least `2C` for `0 < α <= 1`. With a fixed arity and a fixed binary base sorter,
the theorem's squared logarithm instead yields quadratic-log depth. The
asymptotic hypothesis also fails at the final fixed-arity levels.

Thus the remaining question is whether the cube / s-sorting structure can be
used without independently fully sorting every high-arity comparator, or
whether some finite-parameter version has a substantially different useful
contract. Any proposed recursive arity schedule must include all replacement
depths, padding, partial blocks, and terminal binary sorters; do not multiply
headline asymptotic constants without checking their ranges and error terms.

**First deliverable:** formalize the composition inequality and verify the
`2C/α` calculation, then identify a concrete use of the paper's structured
intermediate states that avoids full independent replacement. If no such
interface emerges, record the black-box route as quantitatively uncompetitive
and stop before formalizing the full construction.

**Acceptance:** either a self-contained finite construction and proof of
`limsup D(n)/log₂ n < 200`, or a precise barrier showing that the stated
k-sorting theorem plus black-box binary compilation cannot improve the
coefficient.

**Source:** [paper PDF](https://kozmath.github.io/papers/upper_bounds.pdf),
[LIPIcs DOI](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2024.50).
The first relevance screen, including the s-sorted invariant and binary cost
checks, is in [`experiments/k-sorting-2024`](../experiments/k-sorting-2024/README.md).

## UB-09 — Extract finite-M constants from Chvatal's M-sorter construction

**Priority:** P1 · **Status:** research · **Focus:** finite-parameter analysis of a published global architecture.

Chvatal's DCS-TR-294, Theorem 1.2, gives a global network built from M-sorters
of depth `(48 + o(1)) log_M n + 115` as `M` grows; §8 improves the asymptotic
coefficient to `24 + 16√2 ≈ 46.627`. Replacing each M-sorter by a binary
sorter of depth `d₂(M)` would give binary slope `c_M * d₂(M)/log₂ M` if the
finite-M theorem supplies slope `c_M` and an additive term independent of n.
For Batcher bitonic sorters, the threshold for a slope below 200 is `c₁₆ < 80`
or `c₃₂ < 66⅔`.

The asymptotic `o(1)` alone does not certify either finite arity, and the
published construction is not the reported private sub-10 M-sorter result.
Extract the actual parameter-dependent bound before claiming the arithmetic
target.

**First deliverable:** derive and verify a finite formula for `c_M` from
Chvatal §§1–8 at `M=16,32` (or another arity), include all finite overheads,
and compare binary base sorters. If no usable bound follows, document the
obstruction rather than treating the asymptotic coefficient as a finite result.

**Acceptance:** explicit finite parameters yielding a binary limsup coefficient
below 200, followed by a formal global theorem in the canonical model.

**Source:** [Chvatal DCS-TR-294](https://users.encs.concordia.ca/~chvatal/aks.pdf).

## UB-10 — Recover the reported private sub-100 AKS construction

**Priority:** P3 · **Status:** speculative · **Focus:** literature recovery, not numeric extrapolation.

Seiferas reports that Komlos privately claimed a binary sorting-network depth
around `60–100 log₂ n`, alongside a multiway M-sorter coefficient below 10.
Neither figure is a published theorem or a finite parameter table. Chvatal's
published construction reaches 1830 in binary depth and about 46.6 in its
M-sorter asymptotic framework; that does not reconstruct the private claim.

**First deliverable:** search for a public presentation, technical report, or
precise statement of Komlos's multiway construction. Record the actual
primitive contract, finite parameters, and binary expansion. Do not treat the
reported estimate as evidence for a numerical bound until those are found.

**Acceptance:** a citable construction with enough details to reproduce its
global schedule and binary depth, or a documented conclusion that the lead is
not presently recoverable from public sources.

**Source:** Seiferas, *Sorting Networks of Logarithmic Depth, Further
Simplified*, Algorithmica 53 (2009),
[DOI](https://doi.org/10.1007/s00453-007-9025-6).

## UB-11 — Price cumulative boundary displacement in the profile scheduler

**Priority:** P1 · **Status:** in progress · **Focus:** close the rank-1
transfer before selecting a new multiway stage.

The direct-multiway profile-potential screen had tentatively charged parent
rank-1 outsiders once across disjoint child outputs. That is not justified:
outsiders also shift every ordered address/rank cut. With exact child counts
and all even `pi` outsiders on one side, the 64 rank windows have about
`32*pi` total address mismatches. Summing the existing per-child theorem
gives the safe but coarse coefficient `64` on the parent outsider mass, plus
child-defect terms. Therefore the earlier `alpha=1/2`, sub-0.508 contraction
screen is invalid. A weighted contraction is not ruled out; it requires
recomputing with a smaller level weight and closing the fresh-error and
terminal-purity budgets.

**First deliverable:** prove a finite ordered-partition inequality bounding
the total wrong-address mass in the rank windows by the cumulative cut
displacements, with the two fringe regions explicit. Then substitute the
vector of child-count defects and left/right parent-outsider counts to get
the sharpest usable rank-1 transport coefficient. Identify a stage guarantee
that controls this quantity, if one is needed beyond `NodeSpec`.

**Acceptance:** a checked theorem (or a fully stated abstract theorem plus
Lean proof) that replaces the per-child `64`-fold charge; update the weighted
transfer matrix with the proved coefficient and show whether its full
forcing/terminal budget can close. If it cannot, record the quantitative
barrier and revise the stage contract before network search.

**Working notes:** [`direct-multiway/TRANSFER-AUDIT.md`](../experiments/direct-multiway/TRANSFER-AUDIT.md),
especially “Exact joint decomposition to target” and “Boundary-displacement
calculation and a necessary correction.”
