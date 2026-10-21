# Lateral line repair with an energy-method residual lemma (proposal, 2026-10-21)

Claude (Opus 5.5). **Claim level: model plus a proof plan.** Nothing is proved yet.

## Idea

At every tree level, the nodes in rank order form a line. After each separator, rank-adjacent nodes
(siblings **and cousins**) merge-exchange their columns: bitonic merge of column c of one with column c
of the other, keeping the m smallest on the left. This costs `2 lg(2m)` layers per stage, in two phases.
All levels run in parallel.
* **Bulk.** A separator's crossing error at a cut, `ε_B a/2` keys, is mostly adjacent-range spill. The
  merges cancel it symmetrically (UB-20's Lemma 3: the wrong-side count never increases). So it stops
  being charged to the order-0 budget. That is **ε_B tolerance** (UB-40).
* **Fringe.** A low extreme key of node x that escapes into x's child 1 belongs to `x−1`'s child k,
  which is x's child 1's **cousin** on the line. The cousin merge repairs it. Fringe escapes of
  adjacent-range keys then no longer need to be tiny, which relaxes f and the row floor
  `m ≥ 2(f+1)/p`. This is what "fringe away" idealizes.

## Pricing (`../sub500-screen/screen.py`; tolerance T, plus `2(q+1)` per stage for the merges)

| T | 1 | 5 | 10 | 36 |
|---|---:|---:|---:|---:|
| band + merge-first, fringe /5.8 | 604 | 582 | 566 | 525 |
| band + merge-first, fringe away | 579 | 477 | 428 | **316** |

Below 500 needs both levers: tolerance ≳ 5 **and** the fringe off the row count. Tolerance 36 with the
fringe away gives about 316.

## Why UB-20 was parked, and why that can change

`../lateral-repair/VERDICT.md`. The binding obstruction is the per-column overflow
`Σ_c (|p_c − q_c| − f)₊`, i.e. residual beyond the fringe rows going down as order-1 error.
* With a union over round-2 profiles, the entropy floor is about 510 keys per column, which is
  100–500× the budget.
* The verdict names the fix: "exploit round 1's randomness jointly instead of a union over all
  intermediate states."

That is what the route (d) machinery does (`../fringe-duality/ROUND1-ENERGY.md`):
* round-1 energy on round-2 **source sets**, using the Kingman MGF lemma;
* the n-uniform collision lemma, which needs no profile union.

**Energy heuristic.** Raising a round-2 column W above its mean costs about `W³/3` of round-1 energy, and
the total energy is about 2j. So the adversarial total overflow is about `3.5 j/f²`. At UB-20's numbers
(`λ ≈ 5e4` spill per column, `f ≈ 3e3`, `m ≈ 2^21`) that is about `3e-9` of the parent's wires, against a
budget of `1e-7 – 1e-6`.

## Lemma plan

Write `overflow ≤ Σ_c (|p_c − λ| − f/2)₊ + (same for q)`. For each sibling:
1. **Upper tail** `Σ_{v∈S} (w_v − λ − f/2)`: route (d)'s `escapes` with threshold `f′ = λ + f/2`, mass
   `j = λn`, and `b = λ`, for small and medium `|S|`.
2. **Lower tail (holes).** The plain duality fails, because the walk to row m has positive drift. Use the
   complement inside the strip of rows below b instead: reverse the rows, so the holes form a top
   staircase of mass `Σ (b − h_c)₊ ≤` the relocated mass. Then apply the excess lemma.
3. **Large sets.** Since `Σ_v (w_v − λ) = 0`, `escapes(S) ≤ holes(V∖S) − (f/2)|S|`.
4. **Composition** with the invariant: drift `|P − Q|`, far keys at `O(ε_B²)`, the two phases, and cousins
   across subtrees. These are UB-20's open items 1–2.

## First deliverable

An evaluator for items 1–3 at UB-20's parameters and at the R1 parameters. Then price the
re-derived tolerance T and fringe relaxation with the real merge cost.
