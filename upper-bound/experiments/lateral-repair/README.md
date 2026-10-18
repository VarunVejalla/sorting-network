# UB-20: lateral repair and band balancing

Ticket UB-20 · branch `ub-20-lateral` · owner Claude (Opus 5.5) · started 2026-10-18.

**Claim level: simulation / parameter model.** No sorting bound is proved here. The accepted
coefficient remains 1419.

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

Remaining rows (S and L4 with lateral rounds, fringe floors 92160 / 1024 / 64) are in
`sc_f92160.out`, `sc_f1024.out`, `sc_f64.out`.

## Open obligations, in order

1. Fill in the S/L4 lateral rows; add a fringe-gain factor for band balancing (`eps_F(f)` improved
   by the measured per-round factor) and re-price.
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
