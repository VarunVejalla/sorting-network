# UB-09: ideal-limit screen of the M-sorter tree

Date: 2026-11-02. Claim level: **model** (Chvátal's constraint system with
attack-level separator constants). No new sorting bound.

## Verdict

The M-sorter framework is not a separate route to sub-300. Theorem 1.1 of
DCS-TR-294 (1830) *is* Theorem 1.2's construction with Batcher m-sorters at
m about 2^60, so the repository's binary line (1830, 1419, 789.75) already
lives in this framework. The binary coefficient is

    slope = L(L+1)(x+y)/(xz),   k = 2^x, A = 2^y, nu = 2^-z, m = 2^L,

two Batcher sorts of depth L(L+1)/2 per tree step. (6, 12, 6, 60) gives 1830.

Even with attack-level separators, which no proof could certify, Chvátal's
tree constraints (4.2)-(4.5) and (5.1) bottom out at **about 300**. Getting
clearly below 300 in this framework needs a sharper *tree analysis*, not
sharper separator certificates. The optimum sits at small arity (k about 3)
and m about 2^12, not at large M.

## Inputs

- Property B: `eps_B = C_B / sqrt(m)`. The bulk leak in rows is
  `eps_B m / 2`, so the D2 measurements at m = 8192
  (`sub300` worktree, `prefix-flux/D2-SPATIAL-INVARIANT.md` section 11) give
  `C_B = 0.39` (certified, 17.7 rows) and `0.084` (attack, 3.79 rows). The
  paper's `sqrt(2(1+ln m))` is about 4.5.
- Property F: `eps_F(f, u)` from the exact capture attack
  (`scripts/fringe_attack_scan.py`, n = 500, one seed), with `u = j/(f n)`
  the capture ratio and `delta_F = u`. Zeros are kept as zero, and the
  fringe f is the structural one, `f = m * f_over_m(k, A, nu)` from (5.3).
  Attack values are lower bounds on the worst case, so this is optimistic.

| f rows | u = 0.25 | 0.5 | 0.75 | 1.0 |
|---:|---:|---:|---:|---:|
| 4 | 0.0640 | 0.0990 | 0.1407 | 0.2030 |
| 8 | 0.0180 | 0.0305 | 0.0590 | 0.1177 |
| 16 | 0.0035 | 0.0077 | 0.0192 | 0.0659 |
| 32 | 0 | 0.0014 | 0.0040 | 0.0356 |
| 64 | 0 | 0 | 0.0007 | 0.0183 |

At u = 1, `eps_F` is about 1.1/f.

## Results

Real (non power-of-two) x, y, z, L are allowed, which is also optimistic.

| `C_B` | `delta_F` | Min slope | x, y, z, L | f rows |
|---:|---:|---:|---|---:|
| 0.39 | 0.25 | 508.8 | 1.90, 4.55, 1.45, 14.25 | 39.5 |
| 0.39 | 0.5 | 381.9 | 1.90, 3.75, 1.75, 14.50 | 64.0 |
| 0.39 | 0.75 | 351.4 | 1.60, 3.05, 1.45, 12.75 | 44.8 |
| 0.39 | 1.0 | 471.7 | 1.30, 2.35, 1.25, 14.00 | 223.8 |
| 0.084 | 0.25 | 341.2 | 2.70, 4.55, 1.95, 15.25 | 32.3 |
| 0.084 | 0.5 | 305.0 | 1.20, 2.45, 1.15, 10.25 | 18.1 |
| 0.084 | 0.75 | **299.7** | 1.60, 2.55, 1.35, 12.00 | 38.9 |
| 0.084 | 1.0 | 441.8 | 1.20, 2.15, 1.15, 13.00 | 143.0 |

Decoupled floors, with `eps_F` set to 0 by hand:

| Case | Min slope |
|---|---:|
| Paper `C_B`, `delta_F = 1/25` | 1520.6 |
| Certified `C_B`, `delta_F = 1/25` | 980.7 |
| Attack `C_B`, `delta_F = 1/25` | 700.5 |
| Attack `C_B`, `delta_F = 1` (fringe of about 2 rows; not realisable) | 109.9 |

So the fringe's capture range `delta_F` is the main separator knob, and the
paper's `1/25` alone costs a factor of more than 2.

### Tree-analysis sensitivity (attack `C_B`, `delta_F = 0.75`, coarser grid)

| Change to (4.2)-(4.4) | Min slope |
|---|---:|
| None | about 300 |
| Slack term (Lemma 4.2's capacity misfit) set to 0 | 220.6 |
| `mu` cap (4.3)/(4.4) doubled | 262.6 |
| Sibling term set to 0 | 279.0 |
| All three | 191.7 |

## What this means

- The question UB-09 asked, whether small finite M opens a sub-300 route,
  is answered no. The framework's ideal at attack-level separators is about
  300, and the certified bulk constant alone puts it at 351.
- The remaining lever is the tree recurrence: the capacity-misfit slack, the
  `mu` caps and the sibling charge. These are the terms the later
  repository analyses (tapered, profile scheduler, R1) rework, so this
  screen does not price those analyses; it prices Chvátal's.
- Sub-300 in a tree of this type needs both near-attack separator
  certificates and a tree analysis roughly 1.5 times sharper than
  Chvátal's. Either alone is not enough.

## Limits

- Chvátal's constraint system as transcribed in `chvatal_param_search.py`;
  the repository's improved tree analyses are not modelled.
- Batcher m-sorters; no better binary sorters are known at m about 2^12.
- The attack table is one seed at n = 500 and is extrapolated beyond f = 64.
- `C_B` is assumed to scale as `1/sqrt(m)` from the m = 8192 measurement.
- Integrality, power-of-two parameters, root separator and final sorters are
  not charged (additive or optimistic).

Reproduce: `python scripts/ideal_limit_screen.py` (about 6 minutes),
`python scripts/ideal_limit_screen.py --sensitivity` and
`python scripts/fringe_attack_scan.py --d2 <sub300 prefix-flux path> --seeds 1 --columns 500`.
