# Research track: an invariant that tolerates large per-stage error (few-hundred slope)

> **Update 2026-10-10 (after `../experiments/tapered/`, read `NOTES.md` and `SURVEY.md` there).**
> Corrections to the framing below: (1) Chvátal's invariant is *already* tapered (outsiders of order r
> < μ·δ^r·capacity, δ ≈ μ/5 ≈ 1e-10), so strict-vs-tapered is not the lever; (2) the separator-error
> tolerance is ε_B ≲ μ·Aν ≈ (ν/k)² (via (4.3) μ ≤ ν/(Ak²), (4.4) and the sibling term), not "ν²/(50k)";
> (3) the (4.2) budget at the Lean values is 48% schedule slack, 28% ε_B, 20% sibling term, 2% μ, so a
> larger ε_B alone buys at most ~3.5× before the budget is exhausted, and a locality-aware separator
> interface gives only ~5% (model: 1250–1290 vs 1334 ideal); (4) parameter freedom is exhausted
> ((x,y,z) ≈ (5.8, 9.9, 4.5) already optimal).
> **What does help (model, unproved):** removing the *schedule slack* (an artifact of equal block sizes,
> Lemma 4.2 p. 11) with a non-uniform-block flow table lets A drop from 2^12 to 2^7: ideal 935, windowed
> integer (64, 2^7, 2^-6) ≈ **1025** with today's separator; with also dropping (4.3) (top-node redesign),
> δ_F ≈ 1/2 for two rounds and per-side accounting: ~780 windowed (650 ideal); ~700 only if Property F
> were provable at f ~ 2^10. Below ~600 looks implausible in this family. The concrete next candidate is
> therefore the slack-free flow table (see `../experiments/tapered/NOTES.md` §2.3), not a bigger ε.
> The text below is the original (partly superseded) research plan.

Status: idea + parameter-model evidence only. Nothing here is proved or formalized.

## Why the current architecture stops near 600–1000

Chvátal's network: slope = (depth of one stage) × (stages per bit).

* Stage = sort–scramble–sort on columns of height `m`; depth `2·T(L+1) = (L+1)(L+2)`.
* Stages per bit = `(x+y)/(x z)` for arity `k=2^x`, capacity growth `A=2^y`, shrink `ν=2^-z`
  (currently `(6,12,6)`, i.e. 0.5, so 3540 × 0.5 = 1770).
* The invariant needs ε ≲ (ν/k)² (conditions (4.1)–(4.3): ε* ≤ μ/k, μ ≤ ν/(Ak²), …), about 2^-24…2^-26
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
