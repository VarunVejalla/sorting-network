# Pricing the repository's tree analyses at ideal separators (UB-09 follow-on)

Date: 2026-11-03. Claim level: **model** (optimistic floors). No new sorting bound;
the best proved coefficient is still 789.75.

## Verdict

No existing tree analysis gets below about **380**, even with attack-level
separators. The idealised zero-residual analysis (R3, shown unreachable in
`../slackfree/SLACKFREE.md`) gets 332. Sub-300 is therefore not reachable by
sharpening the tree analysis while the separator stage costs three full sorts.
The lever is the **stage depth at fixed leak**. If the first of the three sorts
were free, the floors become 256 (centred, R2c) and 221 (R3) at attack level,
and 342 at the certified bulk.

## Correction to UB-09-IDEAL-LIMIT.md

`ideal_limit_screen.py` charged **two** sorts per tree step, but its bulk
constant (3.79 rows attack, 17.7 certified at m = 8192) and its fringe table
come from the **three-sort** (two-scramble) stage of the D2 work. The UB-09
floor of about 300 is therefore the "first sort free" figure, not the three-sort
one. The consistent three-sort figure for Chvátal's analysis (R0) is about 460.
The paper's own one-round constant, about 4.5, does match two sorts: 192
certified rows of round-1 spread at m = 8192 gives C_B = 4.24.

## Method

`scripts/tree_pricing.py` uses (4.2)–(4.5) with the residual and the η factor of
each analysis, as written in `../slackfree/feas.py`:

| Analysis | Residual in (4.2) | Status |
|---|---|---|
| R0 | Chvátal's slack (Aνk − 2Aν + 1)/(2A²k²) | proved (1830, 1419) |
| R1 | r* = (k − 1)/(2A²k²), η₁ | proved, the 789.75 proof (design P) |
| R2 | κ(μ + ε_B/2)/(Aν − 1), κ = 1, η₂ | derived, unproved (new invariant Q) |
| R2c | the same with κ = ½ (centred) | derived, unproved |
| R3 | 0 | shown unreachable |

The other inputs:
- **Depth.** The stage depth is 3·L(L+1)/2 per step. The s = 2 column is 2/3 of
  it, because the optimum doesn't move when the slope is multiplied by a
  constant.
- **Bulk ε_B(m), certified.** `walk-bound/na_precision.py`, interpolated. In rows
  it grows like m^(1/4): 22.9 at 2^13, 159 at 2^24, 3771 at 2^42.
- **Bulk ε_B(m), attack.** 3.79 rows at 2^13, scaled as m^(1/4). This is
  heuristic.
- **Fringe.** The attack ε_F table at the structural fringe f = m·f_over_m.
- **Grid.** Real x, y, z, L on a 0.2 grid. There is no rounding reserve, and
  integrality is free.

Check: `python scripts/tree_pricing.py --check` accepts the proved 789.75 point
(4,5,3), L = 26 under R1, and rejects it under R0, as `SLACKFREE.md` reports.

The centred sided invariant (`../sub500-screen/INDUCTION-v6.md`, the sub-500
package's analysis) is a per-node certificate, not a formula. So
`scripts/centred_pricing.py` drives `width_sim.py` directly, with:
- integer triples only;
- far-crossing tails and ROUNDF set to 0;
- δ from (4.5) at the attack ε_F;
- the least integer L at which every sender's order-0 ratio is at most 1.

## Results (minimum slope, three sorts per step)

| ε_B | δ_F | R0 | R1 | R2 | R2c | R3 |
|---|---:|---:|---:|---:|---:|---:|
| certified | 0.5 | 566 | 515 | 532 | 513 | 475 |
| certified | 0.75 | 552 | 517 | 547 | 526 | 471 |
| certified | 1.0 | 725 | 693 | 743 | 696 | 601 |
| attack | 0.5 | 463 | 413 | 402 | **384** | 332 |
| attack | 0.75 | 460 | 425 | 443 | 418 | 354 |
| attack | 1.0 | 675 | 651 | 705 | 658 | 543 |

The optima sit at k = 3 to 8, A about 2^2.5 to 2^4, and m about 2^12 to 2^16,
with fringes of 45 to 185 rows. R2 can lose to R1: its ε_B-dependent residual
and η₂ cost more than r* at small Aν.

Centred sided invariant (`width_sim.py`), integer triples, three sorts:

| Triple | Attack (δ_F, L) | Certified (L) |
|---|---|---|
| (3,4,3) | **399** (0.5, 18) | 539 (21) |
| (4,4,3) | 420 (0.5, 20) | 600 (24) |
| (3,5,4) | 420 (0.5, 20) | 600 (24) |
| (2,4,3) | 459 (0.5, 17) | **513** (18) |
| (2,3,2) | the design breaks: the prefixes meet at botDesc | |

At certified bulk, the (4,4,3) row reproduces the sub-500 package's three-sort
figure, 600 at L = 24 (the package's 477 uses a cheaper merge-first stage).

## Sorts per step

| Ideal floor | Three sorts | First sort free (s = 2) |
|---|---:|---:|
| Best proved analysis (R1), attack | 413 | 275 |
| Best analysis on paper (R2c or centred), attack | 384 | 256 |
| Zero residual (R3), attack | 332 | 221 |
| Best analysis, certified bulk | 513 | 342 |

## What this means

1. Tree analysis alone is not enough. Going from the proved R1 to an ideal zero
   residual is worth only about 20% (413 → 332). Every realistic analysis sits
   at 380 or above, at three sorts.
2. Sub-300 needs a separator stage that costs well under three full sorts for the
   two-scramble leak. Merge-first wiring (UB-44) is the existing step in this
   direction, but at q = 24 it saves only 55 of 900 levels.
3. Even with a two-sort-cost stage, sub-300 needs attack-level bulk: the
   certified bulk gives 342. So two things are needed together: a cheaper stage
   at the same leak, and a bulk certificate within about 1.5× of attack.

## Limits

- **Optimism.** These are lower bounds for each analysis: real parameters,
  attack separators, zeros kept as zero in the fringe table, and no rounding.
- **Attack bulk scaling.** Assumed to be m^(1/4) from a single m = 8192
  measurement.
- **Coarse grids.** δ_F is on {0.5, 0.75, 1.0} and the grid step is 0.2.
- **Centred runs.** Depth d = 14, with the tails set to zero.
- **Merge-first.** "First sort free" is a floor for merge-first designs, not a
  model of them.

Reproduce:
- `BULK_CACHE=<file.npy> python scripts/tree_pricing.py` (about 15 minutes; the
  first run builds the bulk table);
- `python scripts/centred_pricing.py --sim ../sub500-screen` (about 10 minutes).
