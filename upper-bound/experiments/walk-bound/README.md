# UB-29: Property B without the union over input states

Ticket UB-29 · branch `ub-29-walk-bound` · Claude (Opus 5.5) · 2026-10-18. Start with
[WALK-BOUND.md](WALK-BOUND.md) (round 1), then [ROUND2.md](ROUND2.md) (round 2), then
[FRINGE-CERT.md](FRINGE-CERT.md) (certified fringe and exact Chvátal conditions at the 1326 point).

**Claim levels.** Both rounds are hand proofs, each reviewed once by a fresh-context reviewer. The
deterministic steps are checked exhaustively on small cases. Every slope below is a parameter
model. The walk-bound constants are floating point; the fringe at the 1326 point is
interval-certified and its Chvátal conditions are checked in exact rationals. Nothing here is in
Lean, and the accepted coefficient is still 1419.

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
| **V0 Chvatal as is, certified-route fringe at the needed precision** | 1297 (1419) | 1210 (1326) | **1197 (1326)**, fringe binds |
| S, slack removed (UB-12) | 893 (999) | 758 (866) | 708 (818) |
| L4', `delta_F = 1/8` | 690 (792) | 568 (677) | 539 (630) |
| L4', `delta_F = 1/5` (tapered L-items, top-node redesign assumed) | 626 (726) | 552 (650) | 529 (632) |

The certified-route rows were recomputed on 2026-10-19 after fixing a model bug: `eps_F` had been
taken at `eps_B = 0` (FRINGE-CERT.md §1). Outputs: `reprice_b.out` (sketch) and `reprice_na_b.out`
(proved round 2). In V0 the fringe binds, so the stronger bulk does not move it, and further V0
gains need a better fringe. The variants with fringe headroom (S, L4') gain another 20–50.

## Near-term candidate: 1419 → 1326 with the same construction

The V0 row uses no structural change, only re-chosen parameters and stronger proofs (FRINGE-CERT.md):
`(k, A, nu) = (64, 2^11, 2^-5)`, `mu = (1 - 2^-10) 2^-28`, `delta = 1.38e-9`, separator
`lg m = 38` with `eps_B = 2^-25`, fringe `f = 32760` rows at `delta_F = 128/4095` and
`J = 1/eps_F = 1.15e7`. The stage costs `3 T(39) = 2340` layers at 17/30 stages per bit, giving
1326.

Obligations, in order:

1. ~~Prove round 2 of the walk bound.~~ **Done (hand proof, reviewed): ROUND2.md.** It remains
   to interval-certify its constants: a lower enclosure of `theta*`, and the sup over `p` (§7).
   At `lg m = 38`, `d = 1.36e-8` against `2^-25 = 2.98e-8`, a 2.2x margin.
2. ~~Interval-certify the fringe.~~ **Done: FRINGE-CERT.md §2–3 (reviewed).**
   `fringe_cert_v2.py 32760 6552 29484 1 2 5155 11500000 128 4095` gives `ln(2 P1) <= -3496` and
   `ln(2 P2) <= -1286`. This needed one new rigorous ingredient, a tighter R2 tail (§3). The
   Lean-friendly closed forms fail at this point.
3. ~~Chvatal's (4.1)–(4.5) in exact rationals.~~ **Done: `chvatal_conditions.py`.** It reproduces
   the package, and at V0 the binding conditions are (4.2) at 0.996 and (4.5) at 0.990. Still open
   on the package side (FRINGE-CERT.md §5): the flow-table integrality (`FlowSizes7`), `mu c < 1`,
   the `ScrambleGeometry` relation between `f` and `m`, and uniformity in `f`.
4. Then Lean. Freedman's maximal inequality and slice McDiarmid (round 1), negative association of
   permutation distributions (round 2), and the per-E fringe route are probably not in Mathlib.
   The package is specialized to `(64, 2^12, 2^-6)`.
