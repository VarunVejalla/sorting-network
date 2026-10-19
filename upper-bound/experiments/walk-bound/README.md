# UB-29: Property B without the union over input states

Ticket UB-29 · branch `ub-29-walk-bound` · Claude (Opus 5.5) · 2026-10-18. Start with
[WALK-BOUND.md](WALK-BOUND.md) (round 1), then [ROUND2.md](ROUND2.md) (round 2).

**Claim levels.** Both rounds are hand proofs, each reviewed once by a fresh-context reviewer. The
deterministic steps are checked exhaustively on small cases. Every slope below is a parameter
model, and the constants are floating point (not interval-certified). Nothing here is in Lean,
and the accepted coefficient is still 1419.

## Result

Centering by the mass splits a scramble-and-sort separator's excess into per-column random walks.
The adversary's choice of column heights collapses into one walk maximum per column, and only a
union over output sets remains. This removes the `ln m` of Lemma 6.1:

* **One round:** `E1 = 2 (1.174 sqrt(m) + 2/3)/m` at `n = 16`, `eta = 1/100`, which is
  2.1–3.3x below `sqrt(2(1+ln m)/m)` for `lg m` from 16 to 42.
* **Two rounds (proved, ROUND2.md):** weak duality `sum X_j(delta_j) <= lam R + sum Y_j(lam)`
  with drifted-walk suprema `Y_j`, and negative association of the within-row indicators for the
  product MGF. This gives `d = 2 C2 sqrt(E1/m)` with `C2 ≈ 1.66` at `n = 16`. That is 1.8x below
  the earlier sketch and 5–8x below BULK2. The bulk threshold for the 1419 package's
  `d = 1/59e6` falls from `lg m = 41.66` to **37.57**, uniformly in `n >= 16` (37.53 at
  `n = 16`; the sketch gave 38.65).

## Re-priced designs (`reprice_walk.py`; `reprice_a.out`/`reprice_b.out` sketch, `reprice_na.out` proved)

Ideal coefficient, with the windowed integer value in parentheses.

| design | current proofs | walk round 2 sketch | **walk, proved round 2** |
|---|---:|---:|---:|
| V0 Chvatal as is, original fringe model (92160-row floor) | 1317 (1419) | 1259 (1419) | 1241 (1419), fringe binds |
| **V0 Chvatal as is, certified-route fringe at the needed precision** | 1286 (1418) | 1175 (1326) | **1175 (1326)**, fringe binds |
| S, slack removed (UB-12) | 893 (999) | 758 (866) | 708 (818) |
| L4', `delta_F = 1/8` | 690 (792) | 568 (677) | 519 (630) |
| L4', `delta_F = 1/5` (tapered L-items, top-node redesign assumed) | 626 (726) | 535 (630) | 503 (630) |

In V0 the fringe now binds, so the stronger bulk does not move it. Further V0 gains need a
better fringe. The variants with fringe headroom (S, L4') gain another 30–50.

## Near-term candidate: 1419 → about 1326 with the same construction

The V0 row uses no structural change, only re-chosen parameters and stronger proofs:
`(k, A, nu) = (64, 2^11, 2^-5)`, separator bulk precision `eps_B = 2^-24` (bulk binds at
`lg m = 36.2`), fringe height about 24800 rows at `J ≈ 2^23` (binds at `lg m = 37.6`). The
power-of-two window then rounds up to `lg m = 39`, so the stage costs `3 T(39) = 2340` layers at
0.567 stages per bit, giving 1326.

Obligations, in order:

1. ~~Prove round 2 of the walk bound.~~ **Done (hand proof, reviewed): ROUND2.md.** It remains
   to interval-certify its constants: a lower enclosure of `theta*`, and the sup over `p` (§7).
2. **Interval-certify the fringe** at `f ≈ 24800`, `J ≈ 2^23`. This needs the clamped-`n`
   F2ROUND evaluation (`../lateral-repair/fringe_general_screen.py`, currently a float screen) in
   `mpmath.iv`.
3. **Re-check Chvatal's (4.1)–(4.5)** and the package's integrality and window conditions at
   `(64, 2^11, 2^-5)` with exact rationals. The package's Lean proof is specialized to
   `(64, 2^12, 2^-6)`; generalizing it is a Lean task.
4. Only then move to Lean. Freedman's maximal inequality, slice McDiarmid (round 1) and negative
   association of permutation distributions (round 2) are probably not in Mathlib.
