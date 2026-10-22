# Fringe by duality (UB-34): tabled 2026-10-21

**Status: tabled.** This targets the 731.25 point and does not on its own lead below 500 (see
`../../backlog/sub500-routes.md`, 2026-10-21 update). Everything here is float-level: rigorous in form,
but not interval-certified and not reviewed.

## What is here

| file | content |
|---|---|
| `FRINGE-DUALITY.md` | the double weak-duality fringe argument, and why the plain version fails the dense regime |
| `ROUND1-ENERGY.md` | the round-1 energy problem. Route (d) (energy on round-2 source sets), the Kingman MGF lemma, the n-uniform collision lemma, coverage of all j and set sizes, sweep status |
| `route_d_rigorous.py` | the evaluator: `python -I route_d_rigorous.py sweep <n> <J> <f> <j_from> <j_to>` checks every j in the range and every set size |
| `route_d_model.py` | the earlier heuristic model of route (d) |
| `fringe_duality.py`, `dense_check*.py`, `q_joint.py`, `n_scan.py`, `adversary_energy.py` | the older duality route and the adversary for the round-1 energy |
| `rd_sweep/`, `rd_alln/` | sweep outputs (f = 4000, J = 1.66e6). `rd_sweep_old/` and `rd_runs/` are superseded |

Lean pieces already in `best/AKS/Sub800/`: `FringeDualityDet.lean`, `FringeDualityTail.lean`, and
`FringeDualityProb.lean` (deterministic duality identities, level-crossing tails, the fixed-set MGF via
NA, unions).

## Where it stopped

**Sweeps** (better of Kingman and collision at each level):
* n = 2^18 – 2^26 (n = 2^20 and 2^26 among them): complete through jmax, 0 FAIL.
* n = 2^27 – 2^40: 0 FAIL up to roughly 4e4 – 1e5 J, but not through jmax.
* n = 2^34: 0 FAIL up to 2.8e6 J (jmax 5.2e6 J).
* All were stopped when the work was tabled.
* Below n = 2^18 there are real FAILs. Those n are never used (Batcher threshold 2^43, rows ≤ 2^25).

## To resume

1. Finish the sweeps for n = 2^27 – 2^40 through jmax: rerun the `sweep` command from the last interval
   in each output file.
2. Write the n → ∞ argument, for the sparse regime (the collision branch is monotone in n) and the dense
   regime (`j ∝ n`). See the end of `ROUND1-ENERGY.md`.
3. Replace floats with interval arithmetic, as in `best/notes/two-round/cert_walk.py`.
4. Get the argument reviewed.
5. Lean:
   * NA for a permutation of a weighted vector (`NegAssoc` only covers single sets);
   * the Kingman MGF bound;
   * the collision lemma;
   * the level composition;
   * then a `ColumnF2` fringe interface and an `R1At73125` instance. The bulk `R1Cells25`/`R2Cells25` is
     already kernel-checked.

## Resumed for the sub-500 package (2026-10-22)

The centred package at (4,4,3), q = 24, δ = 1e-6 (`../sub500-screen/INDUCTION-v5.md` §8) needs this fringe
at **f ≤ 3967, J ≈ 5e5**. Separator senders have `a > 2^37`, since the stage depth 716 lets Batcher sort
exactly up to q = 37, so `n ≥ 2^13`.

Sweeps over every j and every set size, with the collision lemma included (`rd_pkg/`):

| n | result |
|---|---|
| `2^13 … 2^17`, `2^20`, `2^26` | **complete through jmax, 0 FAIL** |

Worst cases are −2840 to −1128 at small n, and 7645 against an allowance of 62392 at `2^26`. Runs at
`2^30, 2^34, 2^40` were launched. The earlier harder-point sweeps (J = 1.66e6) cover `2^27 … 2^40` partially.

Still float-level: interval certification, the n → ∞ argument and review remain.
