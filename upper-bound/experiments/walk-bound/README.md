# UB-29: Property B without the union over input states

Ticket UB-29 · branch `ub-29-walk-bound` · Claude (Opus 5.5) · 2026-10-18. Start with
[WALK-BOUND.md](WALK-BOUND.md).

**Claim levels.** The round-1 bound is a hand proof, reviewed once. The deterministic step is
checked exhaustively on small cases. Round 2 is a sketch. Every slope below is a parameter model.
Nothing here is in Lean, and the accepted coefficient is still 1419.

## Result

Centering by the mass splits a scramble-and-sort separator's excess into per-column random walks.
The adversary's choice of column heights collapses into one walk maximum per column, and only a
union over output sets remains. This removes the `ln m` of Lemma 6.1:

* **One round:** `E1 = 2 (1.174 sqrt(m) + 2/3)/m` at `n = 16`, `eta = 1/100`, which is
  2.1–3.3x below `sqrt(2(1+ln m)/m)` for `lg m` from 16 to 42.
* **Two rounds (sketch):** 2.8–4.7x below BULK2. The bulk threshold for the 1419 package's
  `d = 1/59e6` falls from `lg m = 41.66` to 38.65.

## Re-priced designs (`reprice_walk.py`, `reprice_a.out`, `reprice_b.out`)

Ideal coefficient, with the windowed integer value in parentheses.

| design | current proofs | walk-bound bulk |
|---|---:|---:|
| V0 Chvatal as is, original fringe model (92160-row floor) | 1317 (1419) | 1259 (1419), fringe binds |
| **V0 Chvatal as is, certified-route fringe at the needed precision** | 1286 (1418) | **1175 (1326)** |
| S, slack removed (UB-12) | 893 (999) | 758 (866) |
| L4', `delta_F = 1/5` (tapered L-items, top-node redesign assumed) | 626 (726) | 535 (630) |

## Near-term candidate: 1419 → about 1326 with the same construction

The V0 row uses no structural change, only re-chosen parameters and stronger proofs:
`(k, A, nu) = (64, 2^11, 2^-5)`, separator bulk precision `eps_B = 2^-24` (bulk binds at
`lg m = 36.2`), fringe height about 24800 rows at `J ≈ 2^23` (binds at `lg m = 37.6`). The
power-of-two window then rounds up to `lg m = 39`, so the stage costs `3 T(39) = 2340` layers at
0.567 stages per bit, giving 1326.

Obligations, in order:

1. **Prove round 2** of the walk bound: a Bernstein tail for the peeled maxima valid for every
   `p`, and concentration of their sum uniformly over `S` and the base row `i` (WALK-BOUND.md §6).
2. **Interval-certify the fringe** at `f ≈ 24800`, `J ≈ 2^23`. This needs the clamped-`n`
   F2ROUND evaluation (`../lateral-repair/fringe_general_screen.py`, currently a float screen) in
   `mpmath.iv`.
3. **Re-check Chvatal's (4.1)–(4.5)** and the package's integrality and window conditions at
   `(64, 2^11, 2^-5)` with exact rationals. The package's Lean proof is specialized to
   `(64, 2^12, 2^-6)`; generalizing it is a Lean task.
4. Only then move to Lean. Freedman's maximal inequality and slice McDiarmid are probably not in
   Mathlib.
