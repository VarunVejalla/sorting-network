# Wider joint screens and the affine-envelope obstruction (2026-11-11)

**Outcome:** the full integer-middle hull model becomes difficult already on
slightly larger instances. A natural tractable route to a uniform joint bound,
affine envelopes plus the exact first-round support function, has an exact
15.528-row floor on a sampled 8192-row, 16384-column second scramble. It cannot
certify the approximately 12-row target on that instance. This is a method-class
obstruction for fixed scrambles, not a network impossibility or an all-scramble
theorem. There is still no priced proved sub-300 route.

## Bounded wider/taller comparisons

Seed 0, half mass, 30 seconds per model, no further large sweeps:

| n | m | Direct reachable witness | Numerical direct upper | Full-hull outcome |
|---:|---:|---:|---:|---|
| 16 | 4 | 5/8 | 5/8, solver optimal | timeout; witness 3/8, loose upper about 2 |
| 8 | 12 | 7/8 | 7/8, solver optimal | timeout; no conclusive upper |

The direct witnesses are checked by integer simulation. These new direct
upper bounds have not been exhaustively checked, unlike the earlier n=12,m=4
case. A bounded repeat with the known reachable objective supplied as a valid
cutoff found no incumbent within 30 seconds for either hull problem. A missing
incumbent is not infeasibility. No hull gap or equality is established here.
The initial taller timeout exposed an overly strong assertion equating the
solver's excess variables with the actual excess of its feasible profile.
For time-limited solutions those variables can be slack. The scripts now
recompute witness leakage and require equality only on solver-optimal runs.
The hull script saves structured no-incumbent outcomes instead of crashing.

## A deterministic joint upper-bound interface

Fix a final destination set T, first scramble P1 and second scramble P2.
Let phi_v(h) count rows r<h with P2(r,v) in T. For any weights p in R^n define

    H1(p) = max_{actual first-round middles y at mass M} sum_v p_v*y_v,
    R_v(p_v) = max_{h in {0,...,m}} (phi_v(h)-p_v*h).

For every actual input, and every integer middle in the reachable convex hull,

    excess_on_T <= H1(p) + sum_v R_v(p_v) - |T|*M/n.

This keeps joint weighted support rather than a scalar spread. Taking inf_p and
then max_T, divided by n, would bound the total leakage uniformly over inputs.
H1 is exactly the fixed-mass height-choice DP support function.

However, the inf_p relaxation also permits per-column distributions over heights
whose means match a point of the first-round hull. It can mix distant heights
independently in each column. This is a further relaxation of the full hull
model, which evaluates phi at each actual integer middle height.

`d2_joint_hull_flow.py --affine-input <direct.json> --output <certificate.json>`
solves that local-distribution LP for the positive-excess final set of a known
direct witness. It rationalizes both a feasible flow/distribution solution and
support weights. Integer DP and rational replay prove matching upper/lower
values for this fixed-T affine bound, independently of solver accuracy:

| n | m | True/direct global witness | Exact fixed-T affine optimum |
|---:|---:|---:|---:|
| 12 | 4 | 7/12 | 31/48 |
| 16 | 4 | 5/8 | 5/8 |
| 8 | 12 | 7/8 | 33511/30240 (about 1.10817) |

The fixed-T values do not upper-bound all T. They expose precisely the additional
loss in the proposed analytic relaxation. Replay command: `--verify-affine`.

## Exact 8192-row floor, independent of first scramble

Set c=m/2 and M=n*c. The uniform middle y_v=c is actually reachable for EVERY
first scramble: choose every input height equal to c. Thus H1(p)>=c*sum p_v.
For each column choose any distribution over heights with mean c. Pointwise,

    c*p_v + R_v(p_v) >= E[phi_v(height)].

Summing shows that every choice of affine weights costs at least

    (sum_v E[phi_v(height)] - |T|*c)/n.

Use only the nine heights 0,m/8,...,m. In each column select the best two-point
mixture straddling c (or height c alone), with exact rational mixing weights.
Take T to be the first half of destination columns. For independently sampled
uniform row permutations, the resulting replayable exact floors are:

| n | m | P2 seed | Exact floor | Decimal rows |
|---:|---:|---:|---|---:|
| 256 | 8192 | 0 | 554643/35840 | 15.47553 |
| 256 | 8192 | 1 | 281129/17920 | 15.68800 |
| 256 | 8192 | 2 | 1684049/107520 | 15.66266 |
| 16384 | 8192 | 0 | 26713433/1720320 | 15.52818 |

The last width exceeds the row height, but is not an all-width or asymptotic
statement. A seed here initializes P2 directly, not the two-array Stage generator.
The exact witness uses only reachable uniform middle moments and rational local
height mixtures; it does NOT give an actual network input with this leakage.
It excludes affine-envelope certificates for these P2 arrays, regardless of P1.
It does not exclude specially chosen second scrambles or the full integer-middle
hull bound. Typical behavior of these few seeds is not a probability theorem.

## Source, replay, and next decision

    python upper-bound/experiments/prefix-flux/d2_joint_affine_floor.py --columns 16384 --output <floor.json>
    python upper-bound/experiments/prefix-flux/d2_joint_affine_floor.py --verify <floor.json>

The verifier regenerates each row permutation, checks saved endpoint counts,
and recomputes the proposed two-point mixtures with Fraction arithmetic.
Artifacts are in the ignored main-checkout sub300 cache: d2_affine_floor_*.json,
d2_affine_n12.json, d2_affine_n16_m4.json, d2_affine_n8_m12.json,
d2_direct_n16_m4.json, d2_direct_n8_m12.json and d2_hull_n16_m4.json.
Checks are ordinary exact Python computations, not Lean kernel proofs.

Do not continue generic cut sweeps or attempt an affine-only uniform proof.
A successful joint bound must control actual intermediate-height localization,
including the cost of choosing different height intervals across columns; mere
coordinatewise means permit the artificial mixtures above. Possible research
is a rank-localized/nonlinear potential retaining this information, but no
quantitative argument closing 12 rows is currently available. Compare that
specific missing inequality with the cost of redesigning the stage before
adding more implementation. The global recurrence, capture, startup, terminal
cleanup and depth transfer remain independent obligations.
