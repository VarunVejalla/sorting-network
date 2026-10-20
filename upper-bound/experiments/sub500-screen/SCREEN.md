# UB-37: re-price sweep and structural screen of the R1 route

Claude (Opus 5.5), 2026-10-20. **Claim level: model.** Floats only, no certificates. Every
number is the cost under an idealized hypothesis, not a construction. Script: `screen.py`; output:
`screen.out` (run with `python -I screen.py`, about 15 min).

## The model

It is calibrated to the kernel-checked 789.75 point (R1-PROOF.md):
* **Schedule:** integers `(x, y, z)` with `k = 2^x`, `A = 2^y`, `ν = 2^-z`, so `(x+y)/(xz)` stages per bit.
* **μ** from (4.3)/(4.4), and **(4.2′)** with the design-P residual `r* = (k−1)/(2A²k²)` and the 0.1μ reserve.
* **(4.5)** for `ε_F`. The free δ is chosen to minimise the row count.
* **Bulk:** the walk bound (ROUND2), from the cached two-round table `../walk-bound/na_tables.npz`.
  It matches `cert_walk.out` at `2^25.6` and `2^26`.
* **Fringe:** the certified-route fits `f = a·J^p` (`../lateral-repair/lateral_certfloor_model.py`),
  scaled by 1.32 so that the Lean route's `f = 7934` at `J = 190000` comes out.
* **Rows and cost:** `q = ⌈max(lg m_B, lg m_F)⌉`, and the cost is `stage depth × (x+y)/(xz)`.

**Calibration:** `(4,5,3)` gives **789.8**, with q = 26, bulk floor 25.8 and fringe floor 25.7.

## Single levers (best integer schedule)

| hypothesis | cost | schedule, q | reading |
|---|---:|---|---|
| status quo | 789.8 | (4,5,3), 26 | the bulk and fringe floors coincide |
| δ_F = 1/5 (fit); 1/4, 1/3 (extrapolated) | 800; 850; 850 | | **no gain**: at (4,5,3), (4.3) caps μ at `ν/(Ak²)`, about equal to (4.4) at δ_F = 1/8 |
| `r* = 0` (two-sided invariant) | 630 | (3,3,2), 20 | |
| fringe idealized away | 690 | (4,6,3), 23 | the bulk floor alone |
| fringe `f/10` at the same J | 723.9 | (4,7,4), 26 | the bulk floor then binds |
| fringe `f ∝ J^0.25` | 789.8 | | no gain at (4,5,3) |
| **two sorts per stage** (repair R = 0) | **526.5** | (4,5,3), 26 | the largest single lever |
| two sorts, R = 2(q+1) | 567 | | |
| one-round separator (2 sorts at E1 precision) | 880 | (4,6,3), 32 | **worse**: one round of the walk bound is too weak |
| first sort → merge of `k+1` runs | 618.7 | (3,5,3), 24 | idealized run structure |
| all sorts → merges | 225 | | not a valid model: after a scramble, columns are not runs |
| ε_B tolerance ×10 / ×100 / ×1000 | 789.8 | (4,5,3), 26 | **no gain alone**: the fringe floor binds |

## Combinations below 500

| combination | cost | schedule, q |
|---|---:|---|
| **two sorts + fringe 2.4× smaller** (gate) | **487.5** | (4,5,3), 25 |
| two sorts + `f/10` | 482.6 | (4,7,4), 26 |
| two sorts + fringe idealized away | 460 | (4,6,3), 23 |
| two sorts + `f/100` | 460 | (4,6,3), 23 |
| two sorts + `f/10` + `r* = 0` | 400 | (4,4,3), 24 |
| two sorts + fringe away + `r* = 0` + δ_F 1/4 | 359 | (3,4,3), 21 |
| merge first sort + fringe away + δ_F 1/4 | 483 | (3,4,2), 18 |
| periodic restoration, T = 100, P = 2, fringe away | 471 | (5,8,5), 22 |

## Gates (least improvement factor; geometric bisection)

| route | < 500 | < 300 | < 200 |
|---|---|---|---|
| better fringe (`f/c`), three sorts | never | never | never |
| better fringe, three sorts, `r* = 0` | never | never | never |
| better fringe, two sorts | **c ≥ 2.4** | never | never |
| ε_B tolerance T, fringe idealized away | T ≥ 5.5 | T ≥ 36 | T ≥ 101 (q = 8, at the table floor: unreliable) |
| ε_B tolerance T, `f/100` | T ≥ 6.9 | never | never |
| ε_B tolerance T, `f/100`, two sorts | T ≥ 1 | T ≥ 18 | never |
| periodic restoration (fringe away) | T = 100, P = 2: 471 | T = 1000, P = 4: 302 | T = 1000, P = 8: 208 |

## Conclusions

1. **The accepted point sits where the bulk and fringe floors coincide.** Improving one of them
   alone moves the coefficient little or not at all. Every route below 500 changes at least two
   things.
2. **Two sorts per stage (UB-32) is the key lever.** It appears in nearly every route below 500,
   and three sorts never get below 500 with a better fringe alone.
3. **The cheapest modelled package below 500 is two sorts + a 2.4× better fringe**, i.e. `f ≈ 3300`
   at `J ≈ 190000` and `δ_F = 1/8`. That gives 487.5 at the unchanged schedule (4,5,3) with
   q = 25.
4. **δ_F is not a lever at (4,5,3)**, because (4.3) binds. This corrects UB-33. **Removing `r*`
   is a lever** (630 alone, 400 in combination), and it needs the two-sided invariant.
5. **Below 300 needs a different invariant:** ε_B tolerance ≥ 36× with no fringe floor, or periodic
   restoration with T ≈ 1000. Below 200 is at the model's limits.
6. **Ruled out:**
   * the one-round separator with walk-bound precision (880);
   * larger tolerance on its own;
   * the "all merges" model.
7. **Merge-first is worth re-checking.** At R1 a child column receives about 16 sorted segments of
   about 2^22 from the parent's sorted columns, so the first sort can become a 4-level merge. The
   idealized model gives 618.7 alone. The earlier −16% cap (`runaware/`, UB-13) was measured for the
   1770/1419 windows and is not obviously the R1 geometry.

## Caveats

* The fringe fits for δ_F = 1/4 and 1/3 are extrapolated.
* "Fringe idealized away" ignores the fact that identifying extreme-rank wires is itself a
  separation problem. Read it as an upper bound on what a better fringe mechanism could give.
* Two sorts with R = 0 assumes the third sort's guarantees can be had for free. UB-32 has to show
  which of its guarantees are actually needed.
* Periodic restoration assumes an invariant that lets errors grow by T for P − 1 stages and then
  restores them in one precise stage. No such invariant is known.
* Bulk precision below `2^8` rows is clamped to the table's first entry.
