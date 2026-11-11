# Warm-start separators: reuse the balance the network already has (UB-47)

Date: 2026-11-10. Claim level: **model**, plus exact attack runs (lower bounds) and one
deterministic hand observation. No new sorting bound; the best proved coefficient is still
789.75. This is a new architecture lead, not a candidate network.

## 1. The idea

Every existing separator analysis treats a bag's columns as **arbitrary**: any column heights
at every threshold. That assumption is where the 1/W round-1 tail comes from
(`../chvatal/DESIGNED-SCRAMBLE.md`). Against arbitrary columns no scramble design helps, and the
stage needs two or three full m-row sorts.

In the real network the columns are not arbitrary.
- A bag at stage t + 1 is assembled by fixed wiring from row slabs of bags that were just
  separated at stage t.
- A separated bag is spatially balanced: at every threshold its column heights are within a
  small window ±W of the mean, except for a small deviant mass.
- So every row slab of it is balanced the same way. A new column stacks F such fragments
  (parent slabs and child fringe slabs), so its deviation is at most about F·W.

The new architecture makes this an invariant: *every bag is balanced within ±W at every
threshold, up to a stranger mass.* With that invariant, one stage needs only:
1. **Re-bag** by wiring (free).
2. **One full column sort** S(L). This also cleans every stray cell left by the previous band.
3. **One free row scramble.**
4. **A two-grid band repair** wide enough to cover the stacked window F·W, at depth
   2·S(⌈lg 4FW⌉). The two-grid band repair is `../prefix-flux/D2-TWO-GRID-BAND-REPAIR.md`, in
   the sub300 worktree.

That is about S(L) + 50 levels per stage, against 3·S(L) today.

## 2. Why the height window is enough (hand, deterministic)

Take one round: sorted columns, then a row scramble. Each middle column receives exactly one
cell from each row.

**Window bound.** If every input height lies in [H−D, H+D] at a threshold, then:
- every middle column is all ones below row H−D and all zeros from row H+D upwards;
- so its height is also in [H−D, H+D], and its disorder lies inside that window.

This holds at every threshold, so a band repair covering the window sorts the column exactly.

**Cap.** The same argument gives a cap that never increases: the largest middle height is at
most the largest input height. Consequences:
- **Rare cohorts are captured exactly.** At a threshold with only j keys, every column height is
  at most j/c + FW, where c is the number of columns. So the extreme j keys are inside the top f
  rows whenever j/c + FW ≤ f.
- **The fringe floor disappears.** The multiplicative fringe requirement (Property F, the UB-34
  fringe floor) then holds with δ_F = 0 for every cohort up to (1 − FW/f)·λb.

## 3. Evidence

**Window tail law.** `window_tail.py`, attack, n = 4099, m = 2048. Heights are confined to
[H−D, H+D], with a random target set plus a climb inside the window; each run is exact. The
table gives excess rows per column beyond W:

| D | W = 4 | 8 | 16 | 32 | 64 | 128 |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 0.40 | 0.14 | 0 | 0 | 0 | 0 |
| 32 | 1.62 | 0.95 | 0.42 | 0.15 | 0 | 0 |
| 128 | 4.44 | 3.41 | 2.05 | 1.01 | 0.47 | 0.14 |
| 512 | 10.8 | 9.00 | 7.02 | 4.36 | 2.23 | 1.11 |
| 1024 (= m/2, arbitrary) | 16.3 | 14.4 | 11.5 | 8.10 | 4.55 | 2.35 |

What the table shows:
- **Exact cut-off.** The tail is exactly zero once W ≥ D, as the window bound says.
- **Scaling.** Below that, the tail scales with D, about 0.25·D/W rows, instead of with m.
- **Stacked windows.** With D = F·W the excess is 0.42, 0.95, 1.9–2.2, 3.4–4.4 and 5.6–8.1 rows
  for F = 2, 4, 8, 16 and 32, almost independent of W ∈ {8, 16, 32}.

So the stationary excess is about **0.25·F rows per column**, whatever the band width.

**Correction found during the screen.** A band's far crossings are set by the deviations of the
columns *entering* the scramble, not by the middle counts. That is the REVIEW-v7 / sub500
F-cut lesson. So:
- the band must cover the full stacked window F·W;
- cells escape only from fragments that were already deviant beyond W at the previous stage;
- each new column holds F fragments, each with excess about 0.25·F, so the leak is about
  **0.25·F² rows per column**.

An earlier pricing that ignored this gave 50–150. Those numbers are void.

## 4. Pricing (`warm_start_screen.py`, model)

The tree side is that of `../chvatal/TREE-PRICING.md`. Leak and fringe:
- **Leak:** ε = 2·c·F²/m. c = 0.25 is the attack fit; c = 1.5 and c = 6 allow 6× and 24× for a
  certificate.
- **Fringe:** f ≥ 4FW.
- **Grid:** W ∈ {4, …, 128}, and F = F_mul·k, where k = 2^x is the branching.

| Leak c | F | R1 (proved analysis) | R2c | At (x, y, z, L) for R1 |
|---:|---|---:|---:|---|
| 0.25 | k | 191 | 181 | (2, 4.25, 3.05, 16.5) |
| 0.25 | 2k | 223 | 223 | (2, 4.25, 3.05, 17.5) |
| 1.5 | k | 211 | 209 | (2, 4.45, 2.85, 16.5) |
| 1.5 | 2k | **262** | 260 | (2, 4.65, 3.25, 19.5) |
| 1.5 | 4k | 321 | 319 | (2, 5.05, 3.45, 21.5) |
| 6 | 2k | 304 | 304 | (2, 5.05, 3.45, 21.5) |
| 6 | 4k | 368 | 364 | (2, 5.05, 3.85, 25) |

The same three-sort stage on the same model prices at 413 (R1) and 384 (R2c) at attack level.

- **Fringe term.** Setting the fringe term to zero (`--exact-fringe`, section 2) changes these
  by under 5%, because the leak binds.
- **Optima.** They sit in sane territory: k = 4, A ≈ 2^4–2^5 and m ≈ 2^16–2^22, with W = 4 at
  the grid floor.

**Verdict at model level.** Sub-300 needs F ≲ 2k and a certified leak within about 6× of the
attack. It works with the *proved* tree analysis R1; no new tree analysis is needed. F, the
number of fragments whose deviations add in one new column, is the decisive geometric quantity.

## 5. Kill tests, in order

1. **F in the real layout (cheap; design work).**
   - Write the re-bagging map for design P or Chvátal's k-ary bags: parent slabs to children,
     and child fringe slabs to the parent.
   - Count the fragments per new column whose rows straddle a given threshold.
   - Parent slabs give at least k. The question is whether the child-fringe fragments can be
     laid out so that F stays at or below about 2k, for example one fringe fragment per column
     per side.
   - If F ≥ 4k is forced, the route needs the two-round variant in item 4.
2. **Multi-stage stability (simulation).**
   - Iterate re-bag, sort, scramble and band for 10–20 stages on one chain of bags. Use the
     window attack at each stage, carry the strays, and check that the excess stays near
     0.25·F².
   - The worry is that a deviant fragment feeds the next stage's deviant mass with gain close
     to 1.
3. **Certified windowed walk bound (hand / interval).** Adapt `walk-bound/na_precision.py` so
   that each column's walk runs over the window of 2D rows instead of m. Target: c ≤ 1.5 for
   the F² leak.
4. **Two-round variant if F is large.** Sort, scramble, band, scramble, band. The second round
   sees the round-1 middle deviations, whose tail is about 0.25·F, rather than F stacked
   fragments, so the leak should drop towards 0.25·F. Cost: one more band, about 2·S(⌈lg 4FW⌉).
5. **Bootstrap (additive).** At stage 0 the root bag is arbitrary. Old full separators, or
   bands of shrinking width, bring the window from m/2 down to F·W within about
   log_F(m/W) stages. This is independent of n, but must be written into the schedule.
6. **The invariant proof.** State "balanced within ±W at every threshold, up to stranger mass σ"
   alongside the existing stranger invariant. Prove that the stage map preserves it, with the
   leak charged as new strangers.
   - The deterministic window and cap parts are elementary.
   - The probabilistic part is item 3.

## 6. Other architectures considered (new ideas, not screened)

| Idea | Mechanism | Status |
|---|---|---|
| Warm start without full sorts | Re-bag by interleaving mutually balanced fragments (free) plus one merge across fragment types, instead of S(L). This would make stage cost linear in L. | Unpriced. Band escapes leave stray cells that later bands never fix, so a full sort every R stages is needed. A first model gave about 135–155 at R = 4 but used the uncorrected leak of section 3, so it is void. Worth re-modelling after kill test 2. |
| Exact fringe capture by the height cap | Section 2's cap applied on its own: rare cohorts can never be raised above the largest input height. | A possible fix for the UB-34 fringe floor even in the existing line: needs a height-capped invariant for the extreme thresholds only. |
| Latin scrambles at small nodes | `../chvatal/DESIGNED-SCRAMBLE.md`: when m > n, Latin blocks cut the tail to zero beyond about n rows. | Helps only deep nodes; minor. |

Quickly discarded:
- **Approximate sorter plus repair:** `docs/sorter-repair-barrier.md`.
- **Monotone-circuit amplification:** comparator networks have no fan-out.
- **Constant-depth approximate merges:** fan-in of a depth-d merge is 2^d, so absolute
  displacement can't be bounded.
- **Using the network itself as the column sorter:** helps only when L > 2c.
- **Per-node stage clocks:** the root stays active, so it sets the stage depth.
- **More rounds of small columns:** already ruled out.

Reproduce:
- `python window_tail.py 4099 2048` (about 2 minutes);
- `python warm_start_screen.py` and `python warm_start_screen.py --exact-fringe` (about 3
  minutes each).
