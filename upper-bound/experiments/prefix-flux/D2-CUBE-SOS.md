# Boolean-cube degree-two SOS screen (2026-11-11)

**Numerical screen: unfavorable. Not an exact certificate or network impossibility.**
At 8192 rows, the degree-two cube-aware quadratic-majorant method still misses
our approximately 12-row bulk target, even with an optimistic one-direction
relaxation and only selected prefixes. No improved sorting coefficient follows.

## Contract and reduction

Write x_i = 2 sigma_i in {+1,-1}, K=4096. For every selected prefix k,
seek a common quadratic majorant

    c + x^T Q x >= (1/2) sum_{i<=k} x_i - mu*k.

Absorb the diagonal of Q into c, so diag(Q)=0. Give each prefix its own
multipliers lambda_i for x_i^2=1. Require the residual quadratic to be globally
PSD. Minimize c. This is degree-two SOS modulo the Boolean equalities; it permits
indefinite Q. The trace relaxation of the eventual summed spectral bound costs
at least c. This is an optimistic local screen, not a constructed global bound.

Retain k=0 and geometrically spaced prefix endpoints. Average the SDP under row
permutations inside each block between endpoints. If b_i is the block size and
H is Q on the normalized block-constant subspace, the orthogonal eigenvalue in
block i is -H_ii/(b_i-1). Thus each prefix has constraints

    lambda_i <= -H_ii/(b_i-1)     (b_i>1),
    H_ii=0                      (b_i=1),

and the augmented PSD matrix has top-left H-diag(lambda), last column
-sqrt(b_i)/4 on included blocks (zero otherwise), and bottom-right
c+mu*k+sum_i b_i lambda_i. This reduction preserves all K Boolean variables.
Replacing a whole block by one Boolean variable would give a different problem.
Dropping prefix constraints only decreases the optimum, so a certified floor
for this SDP would be a floor for the full method too.

For round one, mu=0. The actual two-direction maximum contains either one-sided
maximum; hence its spread certificate must cost at least D=2*c_round1.
For round two minimize c+mu*D over mu>=0 directly in the SDP. This allows a
more favorable first-round budget than the full two-direction problem.

## Results

CVXPY 1.8.1, CLARABEL, status optimal:

| Prefix density per octave | Blocks | Round-one c | Optimistic D | Best mu | Round-two objective |
|---|---:|---:|---:|---:|---:|
| 1 | 13 | 40.513287 | 81.026573 | 0.063802 | 12.031446 |
| 2 | 24 | 46.028791 | 92.057581 | 0.069739 | 15.147474 |

Maximum primal constraint violations were below 4e-9. A separate direct
8-variable SDP with the same selected prefixes agreed with the compressed
formulation to 3.9e-9. These checks support the implementation but do not provide
rigorous dual lower bounds. In particular, a feasible primal value alone cannot
certify a method-class no-go. The continuous drift optimization is numerical.

## Reproduce and decision

From the sub300 worktree:

    python upper-bound/experiments/prefix-flux/d2_cube_sos_screen.py --mus 0 --density 2 --coupled --output <ignored-output.json>

The generated coarse and denser results are in the main checkout's ignored
LLM-helpers/sub300-check/artifacts/sub300-structural/prefix-flux cache, named
d2_cube_sos_coarse_coupled.json and d2_cube_sos_coupled.json.

The degree-two Boolean corrections do not look sufficient. Do not invest in
Lean for this rescue on these results. If a rigorous rejection is useful, the
next bounded task is rational dual certification of the 24-block pair of SDPs,
with a conservative first-round floor and a jointly optimized second-round
drift. Higher-degree SOS, joint two-round bounds avoiding the scalar spread
interface, and other stage designs remain untested. This does not rule them out.
