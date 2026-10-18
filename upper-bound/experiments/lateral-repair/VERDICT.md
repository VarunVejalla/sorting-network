# UB-20 verdict: lateral repair does not pay at the provable level

2026-10-18 · Claude (Opus 5.5), after three independent reviews. **Claim level: hand-derived
model plus reviewed sketches. No sorting bound is affected; the accepted coefficient stays
1419.**

## Result

Sibling (lateral) merging after each separator is sound in its mechanics. The cancellation of
symmetric spill, the deterministic placement under full-column merges, and the shift identity
were all confirmed by review. In a cost model with **average-case (Gaussian) tails** for the
per-column residual it lowers the L4'-family slope from about 626–758 to about 560 (632–683
windowed). **With the worst-case tools available (union bounds over intermediate states), the
gain disappears.**

The binding obstruction is the per-column overflow (O-L):

* The merge leaves a residual of `|p_c - q_c|` keys per column. It is routed up only if it fits
  the fringe rows, about `f ≈ nu m/(2Ak)`. Anything beyond goes down as **order-1** error, whose
  budget in Chvatal's (4.5) is `delta mu (A nu)^2 ≈ 1e-7 – 1e-6` of the parent's wires.
* At the model optima the spill per column is `lam ≈ 4–8 x 10^4`, against `f ≈ 2.4–3.4 x 10^3`.
  F2ROUND's truncated-profile machinery needs mass at most `delta f n` and does not apply.
* The only worst-case route left is Bennett plus a union bound over both siblings' round-2
  states. It leaves an entropy floor of about `(2 ln 2(m+1) + ln 2)/theta*` keys per column, with
  `theta*` the largest `theta` such that `2 lam (e^theta - 1 - theta) <= theta f`. At
  `m = 2^21.25`: `f/(2 lam) ≈ 0.031`, `theta* ≈ 0.06`, about 510 keys per column, an overflow of
  about `2e-4`. That is **100–500x the budget** (reviewer's `ovf.py`, rechecked by hand).
* Closing the gap needs about `lg m ≥ 25`, where the design without lateral repair already
  operates (L4' at `delta_F = 1/5`: `lg m = 25.2`, slope 626). So nothing is gained.

The floor is the same input-entropy floor that sets Property B's `ln m`
(`backlog/ruled-out.md`, first item). A sharper worst-case technique would change this verdict.
Examples: counting only states reachable after round 1, or exploiting round 1's randomness
jointly instead of a union over all intermediate states. That is an open problem shared with the
whole sort-based family.

## Other findings (record)

* **The earlier lateral figures (343 / 426 / 480–540) were wrong:** they charged the residual to
  the order-0 budget (COMPOSITION.md §3).
* **The fringe floor at moderate precision is about `7 J^0.5` rows** on the existing F2ROUND route
  (`fringe_general_screen.py`; a float screen). The route needs `delta_F < 1/e`; the tapered
  study's `delta_F = 1/2` is not available on it. This is useful to UB-15 independently of
  lateral repair.
* **The run-aware first sort (UB-13) gives at most 2% in this regime.** Assembled columns contain
  about `2Ak/nu` short fringe runs (README.md, last section).
* **Exact sorting of small nodes does not replace Chvatal's (4.3).** Outsiders already in a node
  are sent down. Every "drop (4.3)" variant (the tapered study's L3/L4 and this branch's L4')
  rests on an unproved top-node redesign.
* **Joint fringe loads** can be handled deterministically, without independent scrambles, by
  `(sum_s w_s - f)_+ <= sum_s (w_s - f/L)_+`. The cost is a per-sibling fringe statement at height
  `f/L`, about +1 in `lg m`.
* **P' as sketched is internally inconsistent.** The drift `D_j` is set by the flow table and the
  outsiders, not by the separator. Its bound `|D_j| <= mu c + max(j, k-j) Delta_1 + slack`
  (Lemma 4.2's sorted-case count) must be carried separately from the `eps_B` spill.

## What would revive the route

1. A worst-case per-column overflow lemma for signed staircases with `lam ≫ f`, beating the
   union-bound entropy floor by about 100x at `m ≈ 2^21`.
2. Or a flow-table redesign that sends the overflow up rather than down (larger fringes at
   nodes that run lateral merges), priced against the stage rate.

Neither is in sight. UB-20 is parked with this verdict.

## Files

`README.md` (history and tables), `COMPOSITION.md`, `LATERAL-LEMMA.md`, `SPILL-LOCALITY.md`,
`LEMMAS-2-3.md` (sketches with their review sections), and `lateral_floor_model2.py` (the final
average-case model).
