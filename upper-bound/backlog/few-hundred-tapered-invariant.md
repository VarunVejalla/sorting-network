# Research track: an invariant that tolerates large per-stage error (few-hundred slope)

Status: idea + parameter-model evidence only. Nothing here is proved or formalized.

## Why the current architecture stops near 600–1000

Chvátal's network: slope = (depth of one stage) × (stages per bit).

* Stage = sort–scramble–sort on columns of height `m`; depth `2·T(L+1) = (L+1)(L+2)`.
* Stages per bit = `(x+y)/(x z)` for arity `k=2^x`, capacity growth `A=2^y`, shrink `ν=2^-z`
  (currently `(6,12,6)`, i.e. 0.5, so 3540 × 0.5 = 1770).
* The invariant needs ε ≲ ν²/(50k) (conditions (4.1)–(4.3): ε* ≤ μ/k, μ ≤ ν/(Ak²), …), about 2^-26
  at `(6,12,6)`. A sort-based separator reaches ε ≈ 9/√m, so `m ≈ 2^58`.
* So the stage depth is about `4 w²` with `w = lg(1/ε)`: the *quadratic* dependence on `w` is what
  hurts. Cheaper separators only change the constant 4 (multi-round: ≈ 2.6; run-aware first
  sort: ≈ 3.5); they cannot beat `m ≥ 1/ε`, i.e. `w` sorts of height ≥ 2^26.

## The lever: larger tolerated ε

Parameter-model slope when the invariant tolerates ε larger by a factor `2^s`
(parameters re-optimized each time, fringe size floor `f ≥ 2^17` imposed, scaled to 1770):

| tolerance | Batcher separator (c ≈ 4) | multi-round separator (c ≈ 2.6) |
|---|---|---|
| ×1 | ~1650 | ~1070 |
| ×8 | ~1260 | n/a |
| ×64 | ~990 | ~645 |
| ×1024 | ~910 | ~590 |

The model flattens near 600–900 because of the `f ≥ 2^17` floor (which keeps `L ≥ ~38`) and the
`2·T(L)` stage cost. A few-hundred slope needs a tolerated ε around 2^-8…2^-12 (columns of
2^16…2^24, stage depth ~ 300–600) **and** a reasonable stages-per-bit count (≲ 1).

## Where the tiny ε comes from, and what to change

In Chvátal's presentation strangers in a bag must stay below a strict fraction `μ` at every
stage, so every stage's mis-sorted mass must be ≤ ν/(A k³)-ish. AKS, Paterson and Seiferas
instead let strangers *decay geometrically with rank distance* (`δ^j`), so a constant-quality
separator suffices; they paid for it with expander ε-halvers (depth ∝ 1/ε). For ε < 2^-4,
sort-based separators are far cheaper than expanders, and (to our knowledge) have not been
combined with a tapered invariant.

Concrete research questions:

1. State a tapered invariant (stranger fractions `μ_j = μ δ^j` at rank distance `j` from the
   correct bag) for the sort–scramble–sort node, with explicit constants.
2. For a node guarantee `NodeSpec`-like in terms of `ε_B` only (what exactly must the separator
   deliver at distance `j ≥ 1`?), derive the exchange rate between ε and stages per bit
   (extra stages needed to clean up strangers). The deliverable of a first pass is a table
   `ε → (slope)`, **not** a Lean proof.
3. Check which separator guarantees degrade gracefully: the bulk bound `ε_B ≈ 9/√m` decays with
   `m`; the fringe (Property F) is the delicate one (`docs/chvatal-fringe-obstruction.md`).
4. Only if the table shows slope < ~600 at a realistic ε, decide whether to formalize.

Starting points in the repo: `docs/seiferas.md` (parameter calculus, constants), `docs/paterson.pdf`,
`docs/dcs-tr-294.pdf` §3–§4 (Chvátal's invariants), `docs/bags.md`,
`upper-bound/experiments/paterson/` (another agent's audit of the Paterson-style recursion,
legacy coefficient 6990.5), `upper-bound/experiments/chvatal/scripts` (parameter search).

## Literature anchors (unverified here)

Paterson 1990: ~6100 lg n; Chvátal (DCS-TR-294): ~1830 (this repo proves 1830/1770); a ~100
claim attributed to Komlós is unverified. Lower bound (Kahale): ≈ 3.27 lg n.
