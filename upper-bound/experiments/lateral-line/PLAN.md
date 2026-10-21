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

## Progress (2026-10-21): dense-regime upper tail

Three fixes to `../fringe-duality/route_d_rigorous.py` make the dense regime (`b = λ ≫` the level
scale) work. The sparse route (d) results are unchanged (n = 2^20, j = J: load 394 → 396).
* **Levels geometric in the offset above b.** Absolute geometric levels put 15000 rows in the first level.
* **Cap `A ≤ u R²`.** Weights are capped at R on u sources, so the exclusion check stops there instead of
  escalating to ∞.
* **λ′ up to 1e4 and κ down to 1e-5.** Large A are excluded with a large drift, since `λ′j ≪ A`.

Upper-tail bound at UB-20's regime (n = 2^16, λ = 5e4 spill per column; target average `< λ + f/2 =
λ + 1500`):

| set size s | 1 | 16 | 256 | 4096 |
|---|---:|---:|---:|---:|
| average load bound − λ | 5411 | 3248 | 2373 | 2129 |
| adversarial heuristic `(6j/s)^{1/3}` | 2700 | 1080 | 430 | 170 |

The single column is within about 2× of the adversary. Large sets plateau near 2100, which is still above
the 1500 target. The remaining loss is entropy: profiles and sets on about `H·s` sources.

**Next:**
1. Tighten the large-set regime. Options: entropy shared across levels; a Boolean per-level count with
   `t ~ ln n` for the lowest levels; the CLT-scale bound for `d ≲ √(λ ln n)`.
2. The holes tail, via the strip complement.
3. The identity `escapes(S) ≤ holes(V∖S) − (f/2)|S|` for sets near n.
4. Then the real UB-20 parameters at the R1 point and the re-priced tolerance.

### Boolean level counts (later 2026-10-21)

`k_bool` counts the sources with `z − b ≥ d` using centred indicator weights. With unit jumps, t is
not capped by R, and the union is only over support sets.
* The drift optimum is tiny, `λ′ ~ sqrt(k/2j)`. With `k ≈ n`, t needs to go down to about `sqrt(2/b)`.
* Exclusion then starts at `d ≈ sqrt(2b·ln(eu/k))`, which is the genuine Gaussian scale of round-1
  columns.
* Added `count ≤ Σ_u (min(z_u, hi) − lo)₊ ≤ A/(4(d−1)) + k`, which handles large S where each source
  serves many rows of S.

Upper-tail average load bound minus λ (n = 2^16, λ = 5e4; target `< 1500`):

| s | 1 | 16 | 256 | 4096 | 16384 |
|---|---:|---:|---:|---:|---:|
| before | 5411 | 3248 | 2373 | 2129 | — |
| now | 5197 | 2840 | 1944 | **1640** | 1639 |

The sparse route (d) check improved slightly (396 → 388). The large-set average is now about 10% above
target. Remaining loss: levels saturate up to an offset of about 700, plus a tail of several hundred.

### Spill locality (UB-20 open lemma 1) with the energy method

`../lateral-repair/SPILL-LOCALITY.md` reduces spill locality to far spill. A full-column merge disturbs
`v_j`'s internal block boundaries only through received keys ranked more than `W ≈ |I_j|/k` below the cut.
Their count is the round-2 bulk excess beyond a **margin** `d0 = W/n_u ≈ m/k²`. The mass is `n(i − d0)` and
the mean is `b = i − d0 ~ m/2`.
* With the union over round-1 states, there is a floor `η/2 = ln(m+1)/m`, whatever the margin.
* The energy heuristic is `3.5 j/d0²`.

Evaluator at `n = 2^16`, `m = 2^21`, `b = 2^20`, `d0 = 8192`:

| set size s | 1 | 16 | ≥ 256 |
|---|---:|---:|---:|
| escape bound | 8.2e3 | 3.0e4 | 0 |

The exact worst case over all s is **3.05e4 at s = 17**, i.e. 2.2e-7 of mn: 31× below the floor.
| fraction of mn | 6e-8 | 2e-7 | 0 |

For `s ≥ 256` the average falls below the margin, so monotonicity gives 0. Against the floor `6.9e-6`
this is about 30× better. Both of UB-20's blocking floors, overflow (O-L) and far spill, are "bulk
excess beyond a margin", and the energy method removes the input-entropy floor in both.

## Pricing with the composition corrections (`../sub500-screen/lateral_screen.py`, `.out`)

COMPOSITION.md §5 conditions in the R1-era screen:
* (4.2-L) budget ≥ `ε_2 η`;
* (O-L) residual fits the fringe rows, with t = 8;
* `δ_F/L` and `ε_F/L`, with L = 2;
* band sized against the order-0 budget;
* `+2(q+1)` per stage.

| package | lateral | without lateral |
|---|---:|---:|
| 3 sorts, fringe /5.8 | 791.7 | 731.2 |
| band + merge, fringe /5.8 | 721.2 | 603.8 |
| band + merge, fringe /5.8, `r* = 0` | 674.3 | 490.0 |
| band + merge, fringe away (at (4,6,3)) | 560.0 | 477.3 (`r* = 0`) |

**Lateral repair does not pay at the R1 point in this model.**
* The far-load factor L = 2 halves μ, so `δ_F/L` per node. Then `r* ≈ 3.8μ` exceeds the order-0 budget,
  and (4,5,3) becomes infeasible.
* (O-L) caps the tolerance at about 15–100×. The residual's Gaussian scale `t·sqrt(2λ)` must fit fringe
  rows `g·m` with `g ~ 1e-4`.
* The merges add `2(q+1)` per stage.

The energy method removes UB-20's worst-case floors (overflow and far spill, see above), but the
**structural** costs (L = 2, r*, fringe fraction g) remain. Revival would need L = 1 (an independent
scramble per sibling index, plus a combined-staircase fringe lemma) **and** `r* = 0`, and even then
it is not better than the non-lateral package.
