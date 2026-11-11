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

> **Update, same day (section 7).** The real re-bagging layout gives F ≈ A/ν = 2^(y+z), not k.
> Sections 4–5 assumed F = k to 4k and are superseded:
> - **Window-only invariant:** the F² leak is confirmed by an exact attack, and warm start
>   prices at 335 (R1) / 307 (R2c) at attack level. That is about 20% below three sorts, but not
>   sub-300.
> - **Back-to-back stages:** deviations contract to a fixed point and the band leaks nothing
>   after two stages.
> - **Variance-type invariant:** the leak is linear in F, about F/16 rows, which prices at
>   284–291 (R1) and 236–250 (R2c).
>
> The new gate is an adversarial variance-contraction lemma for one row scramble.
>
> **Update 2026-11-11 (section 8).** That lemma is provable (Lemma G, from Theorem R2), but it is
> tight against an aligned attack at the stationary budget. Per-stage invariants therefore stay in
> the F² class: 335 (R1) / 307 (R2c) at attack level. The 284–291 figures are void as a provable
> target. Warm start is parked unless a multi-stage reachability argument is found.
>
> **Update 2026-11-11 (section 9).** Multi-stage reachability doesn't rescue it. A stage-0 input
> steers stage 1 to the aligned state (correlation 0.99) and reaches about half the per-stage worst
> case at stage 2. Even granting that factor, the price is 295 (R1) at attack constants. Closed as a
> sub-300 route.

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

## 7. The real re-bagging map and back-to-back stages (2026-11-10, second pass)

### 7.1 Counting F in the layout

Take Chvátal's k-ary bags with capacity n·ν^t·A^l. A separator's output column holds m rows: two
fringe slabs of f = m·fom rows go to the parent, and k blocks of b = (m − 2f)/k rows go to the
children. A bag v at level l, stage t + 1, is filled from stage t as follows.

- **From the parent.** k blocks are shared out, so v gets a fraction π_p = 1/(Akν) of its rows
  from the parent. That is m/(Akν) rows per column, less than one block of b ≈ m/k rows,
  because Aν > 1. One parent block is split across Aν columns of v. At any threshold at most one
  piece carries the parent's deviation: **F_parent ≤ 1** (2 at a block edge).
- **From the children.** The rest, 1 − π_p, comes from 2k child-fringe types (the top and
  bottom of each child). Each fragment is f rows, so one column of v stacks

  (1 − π_p)/(2k·fom) = (A/ν)·(1 − 1/(Ak)²) fragments of each type.

  The fom formula has the factor (1 − 1/(Aνk)) = 1 − π_p precisely so that this cancels.
- **At a threshold** near a child cut, essentially one type straddles: child i's top fringe or
  child i + 1's bottom fringe. Their rank ranges are adjacent and disjoint up to strangers. All
  A/ν fragments of that type straddle together.

So **F ≈ A/ν = 2^(y+z)**. That is 256 at design P (4, 5, 3), and about 160 at the section 4
optimum, against the F = k = 4 assumed there.

### 7.2 Exact aggregated attack (`aggregation_attack.py 32 8 512`)

Setup:
- The child window is D = 32 and W = 8, with 512 parent columns.
- The climb is aimed at the union of the C_v over a random set of parent columns.
- The table gives far-cell rows per parent column, E(dev_v − X)₊.

| F | X = F·W/2 | F·W | 2F·W | 4F·W | Random input, X = F·W/2 |
|---:|---:|---:|---:|---:|---:|
| 4 | 6.23 | 3.83 | 1.78 | 0.61 | 0.008 |
| 16 | 25.0 | 15.0 | 7.17 | 2.42 | 0 |
| 64 | 100 | 59.7 | 28.5 | 9.50 | 0 |
| 256 | 402 | 239 | 114 | 38.0 | 0 |

The leak per parent column divided by F is the same function of X/F for every F. It equals the
single-column window tail e_D(X/F) of section 3: (1.56, 0.94, 0.44, 0.15), against section 3's
D = 32 row (1.62, 0.95, 0.42, 0.15). So leak = F·e_D(X/F).

**Stationary case.** If the invariant only bounds every column by a window, the child's window is
D ≈ X, and the leak is about 0.25·F² rows. The F² law is real for that invariant.

Repricing with F = A/ν (`warm_start_screen.py 0.25,0 1.5,0`) gives 335 (R1) / 307 (R2c) at
c = 0.25, and 411 / 372 at c = 1.5. The optimizer escapes to small A/ν: (y, z) ≈ (1.85, 0.85)
or (2.45, 1.45).

### 7.3 Back-to-back stages (`chain_sim.py F 16384 64 20`)

The chain runs 20 stages at one threshold. The fragments of each new column come from F distinct
old middle columns, the row scramble is exact on the active rows, and strays are kept in the
counts (pessimistic). The adversary acts only through the stage-0 input: either random heights in
±64 or the aggregated climb attack.

| F | Stationary input sd | Input max | Middle sd | Leak at X = 4F (attacked chain) |
|---:|---:|---:|---:|---|
| 4 | 2.4 | ~10 | 1.2 | 5.4 rows at stage 1; 0 from stage 3 |
| 16 | 9.0 | ~40 | 2.25 | 4.9 at stage 1; 0 from stage 3 |
| 64 | 36 | ~150 | 4.5 | 1.8 at stage 1; 0 from stage 3 |
| 256 | 145 | ~600 | 9.0 | 0 at every stage |

What the chain shows:
- **Fixed point.** The input sd is about 0.56·F and the middle sd about 0.56·√F. This is the
  square-root contraction of the variance identity V_mid ≤ L1_in
  (`docs/chvatal-separator-cost-analysis.md`), followed by summing F fragments.
- **The attack fades.** It is diluted within about two stages, and the attacked and random chains
  then agree.

So the F² law comes from the window-only invariant, which lets every column sit at its window
edge at once. It does not come from the dynamics.

### 7.4 What a variance invariant would give

Suppose the invariant bounds the column variance at every threshold, say Σ dev² ≤ σ²·(number
of columns), instead of only a window. Then:
- **Far cells** are bounded by Σ(|dev| − X)₊ ≤ Σ dev²/(4X).
- **Leak.** With the attacked variance taken about 3× the random fixed point (a heuristic
  window-climb estimate), so σ_in ≈ F, a band at X = 4F leaks about F/16 rows per column.
- **Pricing** (`--linear`):
  - at c = 1/16: 284 (R1) / 236 (R2c);
  - at 6× that: 291 / 250;
  - at c = 0.25 linear: 291 / 247;
  - at c = 6 linear: 352 / 323.

  The R1 optima are at small parameters, x ≈ 1.8–2.2 and A ≈ 2^1.9–2^2.5, where the real-exponent
  tree model is least reliable.

### 7.5 Status and next gate

- **Window-only warm start:** not a sub-300 route. Model price 335 (R1) / 307 (R2c) at attack
  level, about 20% below the three-sort stage.
- **Warm start with a variance invariant:** a sub-300 candidate at model level, with only a few
  per cent of margin under the proved R1 analysis (284–291) and more under R2c (236–250).

The deciding lemma is an adversarial variance contraction for one fixed row scramble. For
**every** sorted input whose column deviations at a threshold have mean square at most s², the
middle deviations must have mean square at most κ·s, with κ certified (about 0.3 typical here).
The union over inputs is the hard part, as for UB-29. The walk-bound decomposition (one walk per
column, union over output sets only) is the natural tool.

After that lemma:
- the fragment-sum step (deterministic);
- the far-cell bound;
- the existing stranger invariant with the leak charged as strangers.

Not modelled:
- fresh adversarial content entering a bag at later stages (strangers, new fringe cohorts),
  beyond the stage-0 input;
- the export of strays to other bags;
- integrality of k and A.

## 8. The variance-contraction lemma: provable, tight, and not enough (2026-11-11)

Claim levels:
- **Lemma G** is a hand proof, a corollary of Theorem R2 in `../walk-bound/ROUND2.md`.
- **The tightness result** is exact attack runs.
- **The consequence for section 7.4** follows from these two together.

### 8.1 What is needed, and what Theorem R2 already gives

The leak at stage t + 1 is set by the next stage's *input* deviations. Each of those is a sum over
a fixed group C_g of F middle columns of stage t (section 7.1). So the lemma must bound the
grouped vector z_g = Σ_{T∈C_g} (count(T) − i), not the middle deviations column by column.

**Lemma G (grouped round-2 contraction).**

*Setting.* Take the setting of Theorem R2: n columns, base-row grid Γ of G rows, parameters
(λ_q, t_q), and failure budget η. Add a fixed partition of the output columns into n/F groups
C_g of size F, chosen independently of σ.

*Conclusion.* With probability at least 1 − η over σ, every sorted state c of exact mass n·i with
Σ_j |c_j − i| ≤ R satisfies

  Σ_g |z_g| < 2 · max_{1≤q<n/F} (λ_q R′ + x′_q).

Here x′_q is R2's x_s with s = qF and with ln binom(n/F, q) in place of ln binom(n, s).

*Proof.*
1. **Zero sum.** At exact mass, Σ_g z_g = Σ_T (count(T) − i) = 0. So Σ_g |z_g| = 2·max_J Σ_{g∈J} z_g.
2. **Reduce to R2.** For a set J of q groups, S = ∪_{g∈J} C_g has s = qF columns, and
   Σ_{g∈J} z_g = Σ_{T∈S} (count(T) − i).
3. **Bound.** R2 §2 (reduction, base row, weak duality and grid) bounds this by λ_q R′ + Σ_j Y_j^{S,b}.
   R2 §3–§4 (Ville, and the negative-association product) bound its MGF by M(t_q)^n.
4. **Union.** Take the union over the binom(n/F, q) sets J, the G base rows and the values of q.
   Only unions of groups are needed, so the union is cheaper than R2's union over all S. ∎

**Per-column form.** With R = n·ℓ (input L1 ℓ per column) the dominant term is the same as R2's:
λR′ + E ΣY ≈ n·√(2p(1−p)ℓ), with p = qF/n. The per-group L1 is therefore

  ℓ′ = (F/n)·Σ_g |z_g| ≲ 2C·F·√ℓ, with C ≈ 1/√2 plus a union term.

The union term is smaller than R2's C₂ because only binom(n/F, q) sets are counted. Iterating,
**ℓ′ = 2CF√ℓ has the fixed point ℓ* = 4C²F²**.

The ungrouped L2 version (the lemma as first proposed) also follows from R2: take the concave
majorant B(s) of the set bounds; then Σ_T (count(T) − i)₊² ≤ Σ_k (B(k) − B(k−1))², which is about
ℓ·ln n per column. It is not the quantity the leak depends on, so it is not pursued.

### 8.2 Lemma G is tight within a constant (`budget_attack.py 16384`)

Setup:
- The budget is the stationary state's own input L1, ℓ = 0.45F (chain_sim, section 7.3).
- The adversary uses R2's dual-optimal climb: each column maximises X_j(h) − λ|h|, with λ tuned
  to spend at most the budget, aimed at an aligned S = ∪_{g∈J} C_g.
- The baseline is a random state with the same L1.

| F | Grouped next-input L1, attack | Same, random | Ratio | Leak at X = 4F, attack | Same, random |
|---:|---:|---:|---:|---:|---:|
| 4 | 6.95 | 1.83 | 3.8 | 0 | 0 |
| 16 | 61.3 | 7.42 | 8.3 | 9.57 rows | 0 |
| 64 | 496 | 28.7 | 17.3 | 240 rows | 0 |

The ratio grows like about 2√F: the attack aligns the signs within each group, and a random state
cancels them. That is the gap between Lemma G's 2CF√ℓ and the typical √F·√ℓ. Iterated, it is the
gap between F² and F.

### 8.3 Consequence

- **No per-stage norm invariant gives the linear-F leak.** Section 7.4 assumed the worst variance
  is about 3× the random fixed point; it is in fact about 4F²/F = 4F times it. The attacker's
  state meets the same L1 budget as the typical state. Matching its L2 and L∞ was not tested.
  A pure window (L∞) invariant is already the F² class of section 7.2.
- **So every per-stage invariant prices warm start in the F² class.** That is 335 (R1) / 307
  (R2c) at attack constants and about 410 / 370 with certificate-like constants, against 413 /
  384 for three sorts. It is a modest gain, and not sub-300.
- **The 284–291 (R1) figures of section 7.4 are void as a provable target.**

**What would still rescue the linear-F behaviour.** The back-to-back chain (section 7.3) shows the
aligned state fades when the adversary acts only through the original input. A proof would have
to show that a state aligned with stage t + 1's groups cannot be re-created by stage t's scramble
from any state the invariant allows. That is a *reachability* statement about the composite map
(scramble, group, sort, scramble). Theorem R2's per-column walk decomposition does not reach it,
because the stage-(t + 1) heights are functions of σ_t and of the whole input, not free variables.

I don't see a tool for it. A union over stage-t inputs brings back the (m + 1)^n cost that UB-29
removed. So warm start is parked here as a model observation:
- inherited balance is real and contracts in typical dynamics;
- worst-case per-stage certification costs the F² law, and with it sub-300.

## 9. Multi-stage reachability: the network can re-create the alignment (2026-11-11)

Claim level: exact attack runs (lower bounds for the sampled scrambles), plus the model pricing.

**Question.** Section 8 showed that per-stage invariants admit aligned states. Can a state aligned
with stage t + 1's groups actually be produced by stage t from a state the network reaches? If
not, a multi-stage argument could recover the linear-F behaviour of section 7.3.

**Test (`lookahead_attack.py F n2`).** The geometry shrinks by F per stage as the real layout
does, with no column reuse: n₀ = F²·n₂ and n₁ = F·n₂. The adversary gets the stationary budget of
0.45F rows per column, at stage 0 only.

1. **Target.** Compute δ¹*, the stage-1 input that the per-stage worst case wants: Theorem R2's
   dual climb against stage-2-aligned sets, within the same budget.
2. **Steer.** Each unit of stage-0 height deposits one cell into a known stage-1 group, so the
   stage-0 climb prices each deposit by δ¹* of its group.
3. **Run forward** and measure the stage-2 input.

| F | Measure | Per-stage worst | Lookahead from stage 0 | One-stage attack (aimed at stage 1) | Random |
|---:|---|---:|---:|---:|---:|
| 4 | stage-2 L1/col | 6.90 | 4.00 | 3.27 | 1.82 |
| 16 | stage-2 L1/col | 53.0 | 27.8 | 17.4 | 7.38 |
| | leak at 4F | 4.81 | 0.39 | 0 | 0 |
| 32 | stage-2 L1/col | 185 | 91.4 | 41.1 | 14.1 |
| | leak at 4F | 57.4 | 7.22 | 0.69 | 0 |

How the steered state compares with δ¹*:

| F | Correlation with δ¹* | Stage-1 L1 reached | Budget spent at stage 0 |
|---:|---:|---:|---:|
| 4 | 0.947 | 4.27 | 1.80 |
| 16 | 0.986 | 37.9 | 7.20 |
| 32 | 0.991 | 115 | 14.4 |

What this shows:
- **The map is steerable.** A stationary-budget input at stage 0 reproduces the desired stage-1
  state almost exactly.
- **The reachable worst case is close to the per-stage worst case.** At stage 2 it is within
  about 2× in grouped L1, and 4–6.5× above random.
- **The adversary never needs a large starting state.** The first scramble amplifies the
  aligned part by about 2√F, as in section 8.

So reachability buys a constant factor at most, not the √F per stage the chain suggested.
Section 7.3's fading came from an adversary that never aimed at later stages.

**Pricing even if that factor were proved.** Halving the L1 cuts the F² leak constant by about
4: c = 0.0625 instead of 0.25 at attack level. That gives **295 (R1) / 264 (R2c)**
(`warm_start_screen.py 0.0625,0`), with no margin under the proved analysis R1 before any
certificate loss. Proving the factor would itself need a multi-stage argument, and none is
available.

**Verdict: warm start is closed as a sub-300 route.**
- **Per-stage provable class:** 335 (R1) at attack constants, about 410 with certificate-like
  ones.
- **Reachable-state class:** about 295 (R1) at attack constants.

What survives as reusable lessons:
- the window and cap facts (section 2), including exact rare-cohort capture under a height cap;
- Lemma G;
- the finding that fixed-wiring alignment is the binding adversary: worst cases are set by the
  sets aligned with the next stage's groups, and the input can steer towards them.

## 10. Whole-run (amortized) test: one input cannot hurt every stage (2026-11-11)

Claim level: exact attack runs (lower bounds on the adversary, heuristic optimiser), plus the model
pricing.

**Question.** Section 9 aimed the stage-0 budget at one later stage. Can a single stage-0 input make
stages 1, 2 and 3 all leak at once? If it can't, a potential-style argument would charge the run
roughly one per-stage worst case in total, not one per stage.

**Test (`whole_run_attack.py F nT T`, T = 3).**
- Geometry as in section 9: it shrinks by F per stage, and strays are carried.
- Budget: ℓ = 0.45F at stage 0.
- Leak: (|d_t| − 4F)₊ per column.
- Attacks: a recursive steering aimed at stage k, for k = 1, 2, 3, plus a grid of mixtures.
- Reference: the aligned climb with a fresh budget at each stage.

Leak at stage t, with the input L1 per column in parentheses:

| F | Attack | t = 1 | t = 2 | t = 3 | Total |
|---:|---|---:|---:|---:|---:|
| 8 | aligned climb, fresh budget at every stage | 0.37 (18.6) | 0.44 (18.3) | 0.45 (19.1) | 1.26 |
| | aim at 1 | 0.37 (18.6) | 0 (7.2) | 0 (5.2) | 0.37 |
| | aim at 2 | **2.02** (13.8) | 0.035 (11.0) | 0 (6.7) | **2.06** |
| | aim at 3 | 0.35 (7.0) | 0.34 (8.4) | 0.024 (9.3) | 0.72 |
| | random | 0 (3.7) | 0 (3.5) | 0 (3.5) | 0 |
| 16 | aligned climb, fresh budget at every stage | 8.83 (55.2) | 2.97 (62.9) | 8.62 (57.2) | 20.4 |
| | aim at 1 | 8.83 (55.2) | 0 (17.6) | 0 (9.2) | 8.83 |
| | aim at 2 | 9.14 (38.0) | 0.34 (30.6) | 0 (15.6) | 9.48 |
| | aim at 3 | **11.36** (38.5) | 2.24 (26.3) | 0 (20.9) | **13.6** |
| | random | 0 (7.4) | 0 (7.2) | 0 (6.3) | 0 |

The mixture grid never beat the best pure aim. At F = 16, n₃ = 16, so the stage-3 figures are coarse.

**Reading.**
- **The aligned climb is not the leak maximiser.** Its prices are indicators, which maximise L1,
  not the tail. Graded steering prices give heavier stage-1 tails. So the per-stage worst leak is at
  least 2.02 (F = 8) and 11.4 (F = 16), the bold entries.
- **The leak lands on the first stage after the free input.** Aiming later moves damage to stage 1
  as a side effect; it doesn't sustain it.
  - The best reachable leak at stage 2 is about 17–20% of the per-stage worst.
  - At stage 3 it is about 0–1%.
- **Whole-run ratio.** The best total over three stages is 2.06 vs 3 × 2.02 at F = 8 (0.34), and
  13.6 vs 3 × 11.4 at F = 16 (0.40), i.e. about one per-stage worst in total.
- **The input L1 stays above random at stage 3** (about 3×) but below the band. Reachable states keep
  their L1 and lose their tail.

So, at attack level, the amortized picture holds: after the first stage, the reachable leak falls by
about 5× per stage, to near 0. The optimiser is heuristic, so this is evidence, not a bound.

**Does it matter? Pricing with the leak removed (`warm_start_screen.py c,0`).**

| Leak constant c | R1 | R2c |
|---:|---:|---:|
| 0.25 (per-stage, section 8) | 335 | 307 |
| 0.0625 (section 9) | 295 | 264 |
| 0.05 (about 5× reduction, this section) | 294.6 | 260.6 |
| 0.0125 | 283.9 | 247.2 |
| 0.001 (leak ≈ 0) | **283.9** | **229.0** |

- **Under R1 the leak stops binding near c ≈ 0.0125.** The floor of 283.9 is set by the band and
  fringe terms: f ≥ 4FW and the 2·S(⌈lg 4FW⌉) band sorts. Even a perfect amortized proof leaves R1 at
  284 at attack constants.
- **Certificate-like constants** added about 23% at c = 0.25 (335 → about 411). Scaling the floor the
  same way, which is a rough estimate, gives about 350 under R1.
- **Only R2c, which is derived but not proved, gets below 300 with margin** (229–261).

**Verdict.**
- **Under R1:** amortization is real in the model but cannot carry warm start below 300; the
  non-leak cost of the band is the floor.
- **Under R2c:** the route would need both an amortized proof and R2c, and neither tool exists.
- Warm start stays rejected.
- **What carries over:** reachable leak decays fast with distance from a free state, so a whole-run
  potential is the right shape of argument for any fixed-wiring multi-stage design whose non-leak
  cost is low.
