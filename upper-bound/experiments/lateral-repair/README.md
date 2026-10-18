# UB-20: lateral repair and band balancing

Ticket UB-20 · branch `ub-20-lateral` · owner Claude (Opus 5.5) · started 2026-10-18.

**Claim level: simulation / parameter model.** No sorting bound is proved here. The accepted
coefficient remains 1419.

> **Status (2026-10-18, after two reviews):** the lateral-repair slopes in the "Results so far"
> tables below (343 / 426 / 456 / 480–540) are **withdrawn**. They charged the post-merge residual
> to the order-0 budget; it is order-1 error unless routed up (COMPOSITION.md §3). The corrected
> design merges full columns so the residual leaves through the fringe rows. With the composition
> review's fixes and the provable spill-locality floor (SPILL-LOCALITY.md §7,
> `lateral_floor_model2.py`, `comp4_*.out`), it models at **559–576 ideal (632–683 windowed)** for
> L4' at `delta_F` in {1/16, 1/8, 1/5}, and 620 (713) with slack removal alone. Open: the
> fringe-inflow margin argument, a joint per-column fringe statement, and a restated invariant P'
> (COMPOSITION.md §6). The tables below are kept for their mechanisms and calibrations.

## Question

Every Chvatal-type tree with sort-based separators is limited by the *flux law*
(`../tapered/NOTES.md`, §2.1): keys a separator misplaces across a child cut can only leave
through the child's upward fringe, whose bandwidth is about `delta_F * nu^2 / k` of the parent's
bag. So the separator must reach bulk error `eps_B ≲ delta_F nu^2 / k`, and with sort-based
separators that forces column heights `m ≈ 2^34–2^42` and stage costs `3 T(lg m) ≈ 1700–2700`.
The tapered study puts the family's floor near 500–700 even with every known fix.

UB-20 asks whether a **lateral channel**, meaning comparators between adjacent sibling regions,
can carry most of that repair instead, and what it must achieve for a slope near 250.

## Mechanism

1. **The separator's bulk spill is symmetric.** At a cut row `r`, column `c` with `X_c` keys
   below the threshold spills `(X_c - r)_+` small keys into child `j+1` and `(r - X_c)_+` large
   keys into child `j`. When the block size matches the key count these sums are equal, so the
   spill can be undone by *exchanging* keys between siblings `v_j` and `v_{j+1}` without changing
   either bag's size (an oblivious network cannot change sizes).
2. **What it cannot fix.** Net cut drift (schedule slack, outsider-driven boundary shifts) is a
   count imbalance and must still go through the parent. Removing the slack (UB-12) remains a
   prerequisite.
3. **Construction.** After the siblings' own separators, and before routing, v_j's misplaced keys
   are its largest keys, so they sit at the top of its columns. v_{j+1}'s misplaced keys sit at
   the bottom of its columns. Merge column `c`'s top band of v_j with column `c`'s bottom band of
   v_{j+1} (two sorted segments of height `h`; bitonic merge depth `lg(2h)`) and keep the lower
   half in v_j. This cancels `min(p_c, q_c)` pairs; the residual is `sum_c |p_c - q_c|`.
4. **Band balancing (generalization).** Further rounds pair columns by fixed matchings and apply
   merge-and-deal (UB-25's primitive) to thin bands, spreading per-column excess. Applied to the
   fringe, this attacks the fringe floor, which is the next binding constraint (below).

## Results so far

### Calibration of the cross-sibling residual (`sim_lateral_residual.py`)

Two-round scramble+sort of an extreme set, `m=2048`, `n=512`, 4 trials; `lam` = misplaced keys
per column, `rho = sum|p_c - q_c| / P`. Output: `sim_lateral_residual.out`.

| lam | rho random | rho structured adversary | implied C (model `rho = 2 sqrt(C/(pi lam))`) |
|---:|---:|---:|---:|
| 4 | 0.29 | 0.39 | 0.49 |
| 16 | 0.11 | 0.16 | 0.33 |
| 64 | 0.039 | 0.095 | 0.45 |
| 256 | 0.013 | 0.035 | 0.25 |
| 1024 | 0.004 | 0.014 | 0.15 |

The residual falls faster than `1/sqrt(lam)`; the two-round separator spreads extreme keys more
evenly than independent placement. The adversary is a structured one: after round 1, buying
concentration of `h` in one round-2 column costs about `h^2/2` extreme keys. It is not a proof of
worst-case behavior.

### Band balancing on the fringe (`sim_band_fringe.py`)

`m = n = 1024`, fringe `f = 16` rows, band `h = 4f`; fraction of an extreme set of size `j` that
misses the fringe, maximised over 3 trials. `ancestry` targets every column that feeds one output
column through the fixed matchings. Output: `sim_band_fringe.out`.

| j / (f n) | adversary | R=0 | R=1 | R=2 | R=3 | R=4 | R=5 |
|---:|---|---:|---:|---:|---:|---:|---:|
| 0.25 | concentrate | 0.0120 | 0.0095 | 0.0027 | 0 | 0 | 0 |
| 0.25 | ancestry | 0.0117 | 0.0117 | 0.0039 | 0.0005 | 0 | 0 |
| 0.50 | concentrate | 0.0138 | 0.0100 | 0.0033 | 0.0001 | 0 | 0 |
| 0.50 | ancestry | 0.0138 | 0.0121 | 0.0067 | 0.0022 | 0.0004 | 0 |

After the first round each extra round cuts the miss rate by a factor of 3–6, against the
one-round obstruction scale `1/(2f) = 0.031`. Each round costs `lg(2h) = 7` layers here.

### Cost model (`lateral_selfconsistent.py`, built on `../tapered/exchange_rate.py`)

The baseline is reproduced: no lateral repair gives 1419 at integer `(x,y,z) = (6,12,6)`.

* **Lateral repair alone does nothing for today's design (V0).** With one lateral round the
  separator could run at `eps_B = 2^-16.5` (bulk need `lg m = 28.7`), but the fringe condition
  pins `lg m` at 41 in every lateral setting; best integer slope 1427.
* **Slack-free design (S), no lateral:** 893 ideal / 999 windowed; bulk need `lg m = 36.4`,
  fringe need 27.9 once the fringe floor is lowered to 1024 or 64. So with the slack removed, bulk
  precision is binding, which is exactly what lateral repair relaxes.

* **With lateral repair** (`sc_f*.out`; ideal, with windowed integer value in parentheses):

  | variant | fringe floor | no lateral | 1 lateral round, C=1 | C=8, 2 rounds |
  |---|---:|---:|---:|---:|
  | S | 1024 | 893 (999) | 559 (623) | — |
  | L4 | 92160 | 671 (765) | 682 (777) | 694 (789) |
  | L4 | 1024 | 551 (650) | 456 (564) | 467 (576) |
  | L4 | 64 | 551 (650) | **343 (426)** | 335 (437) |

  At the proved fringe floor (92160 rows) lateral repair gains nothing: the fringe pins `lg m`
  near 38. The gain appears only once the fringe floor is lowered, so **UB-15 is a prerequisite**.

* **Fringe band balancing in the model** (`lateral_band_model.py`, `band_f64.out`,
  `band_f1024.out`) adds nothing at a fixed floor. At floor 1024 the chosen fringe sits exactly
  at the floor (the floor binds, not `eps_F`); at floor 64 the fringe is about 100 rows and bulk
  precision binds at almost the same height. So band balancing's value for the fringe is as a
  route to *proving* a low floor (UB-15), not as a cheaper fringe at today's floor.

### Realistic fringe floors (`fringe_general_screen.py`, `lateral_certfloor_model.py`)

The fixed floors above (92160 / 1024 / 64 rows) are replaced by the smallest fringe height the
existing two-round fringe proof route (F2ROUND) certifies at the precision `eps_F = 1/J` a design
actually needs. The screen re-evaluates F2ROUND's general bounds at the clamped worst point
`n = max(16, E J / D)`. That clamp matters: the original `cert.py` closed forms assume
`n = E J / D`, which is below the proof's `n >= 16` at moderate `J`. It is a float screen,
calibrated on the documented points: it passes 131040 and 92160, fails 91136, and gives about
84000 at the old precision because it maximises over integer subset sizes. Output:
`fgen_J*.out`, `fgen_all.txt`.

| `J = 1/eps_F` | `delta=128/4095` | `1/16` | `1/8` | `1/5` |
|---|---:|---:|---:|---:|
| `2^10` | 234 | | | |
| `2^12` | 474 | 576 | 875 | 1662 |
| `2^14` | 979 | 1192 | 1915 | 2836 |
| `2^16` | 2016 | 2457 | 3447 | 5851 |

The floor grows like `J^0.45–0.52`. **`delta_F = 1/2` is impossible on this route**: its R1a
Chernoff step needs `Delta + 1 > e delta f`, so `delta < 1/e`. The tapered study's L4 variant
(which assumed 1/2) is replaced by L4' at the achievable fractions.

Model with these floors (ideal, windowed in parentheses):

| variant | no lateral | lateral, proved `C=25.3` | lateral, simulated `C=0.5` |
|---|---:|---:|---:|
| V0 | 1286 (1418) | 1227 (1370) | 1224 (1339) |
| S, slack removed | 893 (999) | 682 (755) | 556 (632) |
| L4', `delta=1/16` | 758 (856) | 615 (686) | **480 (583)** |
| L4', `delta=1/8` | 690 (792) | 564 (637) | 490 (608) |
| L4', `delta=1/5` | 626 (726) | **543 (660)** | 535 (660) |

Without lateral repair, bulk precision binds in every slack-free row, and lateral repair removes
13–25%. With the simulated constant, the fringe binds again (for example `lg m` 17.7 fringe
versus 15.3 bulk at `delta=1/8`). The earlier 343/426 figures assumed a 64-row floor and
`delta_F = 1/2`, which this proof route cannot supply. **Current realistic range: about 540
(proved constant) to 480 (simulated constant).**

### Where the remaining cost sits

At the best L4 + lateral point, `(x,y,z) = (3.5, 3.0, 2.5)`, `lg m = 16.7`: stage cost
`3 T(16.7) + 18 = 462` layers at 0.743 stages per bit. The three column sorts dominate. The first
exists only to make input columns monotone (AKS 1992's two-round halver: sort, scramble, sort,
scramble, sort). If a child column is assembled from about `k+1 ≈ 12` sorted segments, merging
them costs about `4 x 18 = 72` layers versus `T(17) = 153`; that would bring this point to about
290. That is UB-13 (run-aware first sort), parked because it saved about 3% at `m ≈ 2^42`; it
should be re-priced at these heights.

## Open obligations, in order

1. Lower the fringe floor (UB-15). Band balancing on the fringe is the candidate mechanism; it
   needs a counting proof, not more simulation.
2. Worst-case analysis: replace the structured adversaries by a counting (union-bound) argument
   for the residual after two rounds plus `R` band rounds, including merge-and-deal rounding bias,
   keys beyond the band height, and all thresholds simultaneously.
3. Check composition in the tree: lateral moves create order-0 outsiders at rate `rho*eps_B`; the
   exchange must not break Property F of either sibling or the next stage's flow table.
4. Only then, a Lean statement of the cross-sibling merge contract.

## Files

* `lateral_gate.py`: parameter-free gate (residual `rho` and lateral depth `G` as free inputs).
* `lateral_selfconsistent.py`: residual derived from per-column statistics; `C` and rounds `R`.
* `sim_lateral_residual.py`: calibration of `rho` for the cross-sibling merge.
* `sim_band_fringe.py`: band-balancing effect on fringe misses.

## Run-aware first sort (UB-13) re-priced at small column heights (2026-10-18)

`RUNAWARE=1 python -I lateral_floor_model2.py` (output `comp5_ra_*.out`). The earlier hope was
that at `lg m ≈ 20` merging a column's sorted runs would be much cheaper than `T(lg m)`. The flow
table rules this out. A node `v` gets only a `1/(kA nu)` share of its wires from the parent's
block; the rest are its children's fringes. Each fringe is a sorted run only
`f ≈ nu m/(2Ak)` rows tall, so an assembled column contains about `R ≈ 2Ak/nu + k` runs (about
1000 at the model optimum). A merge tree then costs `ceil(lg R)(lg m + 1) ≈ 220` layers, against
`T(21) ≈ 236`.

| variant | without run-aware | with run-aware |
|---|---:|---:|
| L4', `delta_F = 1/16` | 560 (632) | 560 (632) |
| L4', `delta_F = 1/8` | 559 (663) | 550 (663) |
| L4', `delta_F = 1/5` | 576 (683) | 573 (683) |

**Verdict: no meaningful gain in this regime** (at most 2% ideal, none windowed). Skipping part
of the first sort does not help either. Leaving `R'` runs per column raises the union bound's
input entropy by a factor of about `R'`, so precision degrades like `sqrt(R' ln m/m)`; even
`R' = 30` would need `m` about 30x larger. UB-13 stays parked.
