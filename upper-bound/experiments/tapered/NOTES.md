# Tolerated error vs slope in Chvátal-type trees with sort-based separators

The cyclic first-round discrepancy idea is audited in
[`CYCLIC-FIRST-ROUND-AUDIT.md`](CYCLIC-FIRST-ROUND-AUDIT.md). The
exact-mass second-round rate at `n=16`, `m≥2^30` is now kernel-checked in
`CyclicBulkRate.lean`, conditional on a height-cap property of the first
scramble and its flip. A concrete large-`n` counterexample rules cyclic shifts
out as a uniform replacement for the first-round F provider. The remaining
gate is formalizing the shift and proving that cap, then combining with R2
and the fixed-16 first-round conditions.

Research note, 2026-10-10, with subsequent 945-candidate work recorded below. The parameter model and separator screen are research calculations; the scratch Lean results are listed separately and do not establish a sorting theorem. Scripts are in this folder:
`exchange_rate.py` (the model, all variants; output in `exchange_rate.out`), `exchange_table.py`
(per-ε tables, `exchange_table.out`), `slack_sensitivity.out`, and `sim_locality.py`
(`sim_locality*.out`). Read `SURVEY.md` first. Chvátal page numbers are the **printed** page numbers of
DCS-TR-294 (printed page = PDF page − 1).

## New conditional sub-1000 screen

[`SUB1000-CANDIDATE.md`](SUB1000-CANDIDATE.md) records an exact-rational
candidate at `(k,A,nu)=(64,64,1/16)`. A two-tailed two-round bulk screen and the
existing fringe floor fit a column height of `2^34`; the conditional depth
price is conditionally 945. The unequal-width window, signed path reserve,
address debt, integer rounding, and variable-slot intruder lemmas now compile
in scratch files `VariableWindow.lean`, `SignedReserve.lean`,
`AddressDebt.lean`, `IntegerRounding.lean`, and `VariableSlots.lean`; see the
saved [proof plan](PLAN-945.md). Lean maps the address-corrected flow to
base-64 bag addresses and checks its one- and two-level real occupancy
identities. It also constructs even up-flows and exact-total integer child
blocks and proves a 69-wire one-step occupancy invariant, conditionally on
each bag's schedule hypotheses. The schedule-specific outsider invariant and
subtree-mass hypotheses remain open. The earlier `+0.0053`
terminal surcharge belonged to the superseded product-profile model and is not
charged by the signed-debt model. Reproduce the scalar screen with
[`sub1000_screen.py`](sub1000_screen.py). This is a research lead, not a bound.

The rounding audit distinguishes signed address debt `d(v)` from integer
occupancy discrepancy `eta(v)`. Lean constructs the balanced integer
allocation and checks positivity of adjusted child targets at the `2^34`
cutoff, under the local flow equations and discrepancy hypotheses.
`VariableSlots.lean` isolates the two-boundary intruder estimate for unequal
slot widths. Applying these local facts to the actual stage/frontier schedule
and proving its variable-width outsider induction are still outstanding.

Seed progress (2026-10-11): `CandidateSeed.lean` now packages the special
root/level-one transitions and the next frontier transition as `FlowSizes`,
with canonical disjoint and complete wire placements through stage 3. The root,
level-one sender, and both stage-two frontier sender shapes have `NodeGood`
providers; the top and bottom frontier geometries are proved by scaling their
row templates. The stage-2-to-3 capacity equations are exact. This still gives
no rank/outsider information about those owned wires, no stage-3 sender
provider, and no extension to a global schedule. The root-to-level-one
outsider base is described below; the next decisive proof is the actual
stage-one-to-stage-two outsider transition.

The root-to-level-one outsider base is now proved as
`candidateSeed_root_child_outsider_bound`: each child's order-1 outsider count
after root fan-out is at most `paperRootEpsB * 64^d`, assuming the root
network's existing `NodeSpec`. `candidateSeed_root_child_tapered_budget`
compares this with `mu * candidateReferenceCapacity d 1 1`. The proof uses
exact native occupancy of the raw root and zero root outsiders, followed by
the two boundary-error clauses. Also, `candidateSeed_stageOne_descendants_empty`
proves exact zero mass below each level-two bag in the stage-one placement.
`VariableWindow.lean` now has generic prefix/suffix cut-count lemmas: moving a
cut across an interval of length `m` adds at most `m` keys. This gives the
input-tail estimates once the stage-one output widths have the right
cumulative profile. The current equal-width seed is short by about `31r` at
the far cut after accounting for its `32r` half-fringe. The address-dependent
end/middle profile in `AddressDebt.lean`, with the bootstrap `C/Q` added to
up-flow, now has a formally checked rational profile and exact integer-wire
split (`RaggedBootstrapFlow.lean`). Ragged stage-one and root stage-two row
profiles, including exact conservation and the stage-three count reset, are
also checked in `RaggedBootstrapGeometry.lean`, `RaggedResetGeometry.lean`,
and `RaggedResetFlow.lean`. `RaggedFlowContract.lean` packages the required
row-aligned cut bounds. These are finite geometry/count results, not yet a
sorting-network transition or an improved global bound. The first stage-one
input-tail gate is now kernel checked in `RaggedStageOneRank.lean`:
`candidate_bootstrap_stage_one_input_tails` derives both signed hL/hR cut
estimates for the actual level-one register, and bounds its two native tails
by `paperRootEpsB * 64^d`, using the root `NodeSpec` and the exact bootstrap
profile identities in `BootstrapTailSlack.lean`. The uniform-flow
`bad_send0_real` interface is still not the right bridge here: its common
width and global lower-tail premise discard the signed per-slot structure.

The exact stage-one bag-card decomposition is also kernel checked in
`StageOneWindowGate.lean` (`candidate_bootstrap_stage_one_card_split`). The
next gate is to compose that count with the input-tail bounds in
`variable_window_wrong_le_signed_path`, then connect the result to the ragged
separator's actual output/rank guarantee. The variable-width profile is not
yet installed in a coherent global scheduler; this work does not prove the
stage-one-to-stage-two outsider transition or an improved global bound.

## VERDICT

1. **Larger tolerated ε alone does not get below ~700.** Chvátal's invariant P (p. 10) is already
   tapered: there are fewer than μδ^r·c outsiders of order r. So "tapered vs strict" is not the lever.
   * The ε_B tolerance follows ε_B ≲ μ·Aν (from (4.2), p. 12), where μ ≤ min(ν/(Ak²), ½δ_F·ν/(Ak))
     ((4.3), (4.4), p. 13). This gives ε_B ≲ (ν/k)².
   * Change only the separator interface (per-side Property B, adjacent-only contamination) and the
     model's best is **~1250–1290** (two-round, ideal cost), against 1334 for the model of today's
     package. That is a few percent.
2. **Sort-based locality is real but helps only modestly.** In mass, misplacements go to adjacent
   blocks; the distance-≥2 mass is O(1/m) ≈ O(ε²). Per key the claim is **false** under an adversary
   for one round (see §4). Locality legitimately buys three things:
   * per-cut instead of per-block ε_B accounting (factor 2);
   * a sibling-contamination multiplier of ~2 instead of k−1;
   * probably a larger fringe fraction δ_F (≈1/2 instead of 128/4095), which is plausible for two
     rounds and unproved.

   None of these touches the two terms that actually bind: the **schedule slack** (48 % of the (4.2)
   budget) and the **top-node condition (4.3)**.
3. **The single most valuable assumption is not about ε at all. It is removing the schedule slack.**
   The slack is the systematic boundary drift caused by equal block sizes (Lemma 4.2, p. 11).
   * Remove it with an inhomogeneous ("non-uniform blocks") flow table and keep everything else as is
     (ε_B = 2^-26, two rounds, current F route). The model then gives **935 ideal / 1025 with the
     power-of-two window at integer (k,A,ν) = (64, 2^7, 2^-6)**, against 1334/1419 today.
   * The gain comes from letting A drop from 2^12 to 2^7. The slack forces Aν ≳ k/2.
   * It is fragile: if only half the slack is removed the model gives 1246, and 90 % removed gives 1084
     (`slack_sensitivity.out`).
   * I think it is plausibly true (argument in §2.3), but it requires rewriting Lemmas 3.1, 4.1 and 4.2
     and the flow table.
4. **Slope < 700 is plausible only if four changes are all made.** These are: no slack, drop (4.3),
   δ_F ≈ 1/2, and per-side/adjacent accounting. With all four (variant L4):
   * **650 ideal / ~780 windowed** at ε_B ≈ 2^-20 with the current two-round fringe floor f ≥ 92160;
   * **528 ideal / ~700 windowed** at ε_B ≈ 2^-12 only if Property F can also be proved at fringes
     f ~ 2^10.

   In that regime the exchange rate is flat: ε from 2^-26 to 2^-12 moves the slope by only ~25 %. The
   (x,y,z) optimum in today's family is already ≈ (5.8, 9.9, 4.5) at slope ~1320 (ideal), so parameter
   freedom is exhausted (confirms the coordinator's (5.6, 10, 4.5)).
   * My judgement: getting **below 700 within this family is unlikely** without also attacking the
     power-of-two/integrality window (~+100–150) and the fringe floor.
   * **Below ~600 is implausible.**

## 1. Where each smallness condition comes from (Chvátal §3–§4)

Notation as in the paper:
* capacity c(i,t) ∝ A^i ν^t (p. 7);
* each node sends π(i,t) wires to its parent and β(i,t) wires to each child (p. 8);
* in the middle range, π/c = (Aνk−1)/(A²k²) ≈ ν/(Ak) and β/c = (Ak−ν)/(Ak²) ≈ 1/k.

Property B (p. 5): at most ε_B·a keys of I_j are placed outside B_j. Property F (p. 5): for
j ≤ δ_F|F|, at most ε_F·j of the j extreme keys miss F.

The invariant **P** (p. 10): every node on level i has fewer than μδ^r·c(i,t) outsiders of order r.
This is Paterson's geometric taper with "distance" = order, i.e. the number of levels the key must climb.

**Lemma 4.1 (p. 11), the sibling term.** Node u holds fewer than (1/k + Δ1/c)c keys addressed below a
child w, where Δ1/c = μδkA²/(1−δ²k²A²). This counts keys of w's range hidden as order-≥1 outsiders deep
in other subtrees. Subtree mass grows like (kA)^depth, so convergence needs δ < 1/(kA). It is structural
and does not depend on the separator.

**Lemma 4.2 (p. 11), the bulk count.** With a perfect sort, B_j would get fewer than
μc + (k−1)Δ − π/2 foreign keys. Here Δ = Δ1 + Δ2 and Δ2 = νc/(Ak²) = c/k − β.

The separator adds ε_B·a. The term (k−1)Δ2 − π/2 = (Aνk−2Aν+1)/(2A²k²)·c ≈ (ν/(2Ak))·c is the
**schedule slack**. Its source:
* the fringe takes π/2 of the smallest keys (child 1's) and π/2 of the largest (child k's);
* every block nevertheless has the same size β < c/k;
* so a perfect sort's block boundaries drift by up to ≈ π/2 against the children's key ranges.

The slack is independent of the separator. ε_B·a is per block, so it covers two cuts.

**(4.1) (p. 12): ε* ≤ μ/k.** This is the root separator only, so it is an additive constant.

**(4.2) (p. 12), multiplied by Aν:**

ε_B + slack + μ(1 + (k−1)·sib + δA²k) ≤ μAν.

The left side counts four things:
* the separator's misplacements;
* the drift;
* u's own outsiders shifting the boundaries, plus siblings;
* order-1 outsiders arriving from v's k children (the δA²k term).

The right side is the capacity growth from u to v, c(i+1,t+1) = Aν·c(i,t).

At the Lean values the shares of the budget are: slack 48 %, ε_B 28 %, sibling 20 %, μ 2 %
(SURVEY.md, reproduced in my check: budget 5.95e-8, slack 2.89e-8, ε_B 1.69e-8, sibling 1.19e-8).

**(4.3) (p. 13): μ ≤ ν/(Ak²).** It is used once, in Lemma 4.4.
* A node that contains any outsider must have c > Ak²/ν.
* Lemma 3.2 (p. 10) shows the only node with π = 0 is the top node α(t) at a moment of descent, and
  that node has c ≤ Ak²/ν.
* So (4.3) says the descending top node has μc < 1 and therefore no outsiders at all, because it has no
  exit upward.

This is an **integrality and boundary artifact**. The top window [2k², Ak²/ν] (pp. 7–10) is set by
even splitting and by the ±1 zig-zag of α. It is not a property of the bulk process.

**(4.4) (p. 13): μ ≤ ½δ_F(Aνk−1)/(A²k²) ≈ δ_F·π/(2c).** All order-(r−1) outsiders of u must fit inside
the δ_F-part of one fringe side, because only that part is covered by Property F. This is the genuine
**exit bandwidth**: π/c ≈ ν/(Ak) is forced by capacity conservation, since the level above is filled by
the k children's up-flows.

**(4.5) (p. 13): ε_F/(Aν) + δ²Ak/ν ≤ δ.** The fringe failures feed order r+1. Together with δ ≲ ν/(k²A)
(from the sibling term) this gives ε_F ≲ ν²/k² and hence the fringe-size requirement.

**The chain.** It is not the backlog's "ε* ≤ μ/k, μ ≤ ν/(Ak²)". (4.1) concerns only the root. The
binding chain is:
* ε_B ≤ μ(Aν − 1) − slack − sibling;
* μ ≤ min((4.3), (4.4));
* the slack requires μ(Aν−1) > ν/(2Ak). With μ = ν/(Ak²) this forces **Aν ≳ k/2**, i.e. y ≥ x + z − 1.

That last requirement is what makes stages per bit (x+y)/(xz) ≈ (2x+z)/(xz) instead of
(x+z)/(xz). The result is ε_B ≲ (ν/k)² at Aν ≈ k (2^-24 at (6,12,6)).

**Inherent vs artifact.**

| Term | Inherent? | Why |
|---|---|---|
| bandwidth (4.4), up to δ_F | yes | flux balance, §2.1 |
| order-1 inflow δA²k | yes | structural |
| sibling (k−1)·sib | partly | (k−1) → ~2 under locality, §2.2 |
| slack | artifact of equal blocks | §2.3 |
| (4.3) | boundary artifact | top node at descent |
| δ_F = 1/25 (paper) or 128/4095 (Lean) | proof artifact | sort-based fringes plausibly allow ~1/2 |

## 2. Can a locality-aware or restructured invariant beat the (ν/k)² law?

### 2.1 A flux lower bound that no relabelling of the invariant avoids

Per stage, the separator at u pushes about (ε_B/2)·a(u) foreign keys across each cut. They become
order-0 outsiders in the child v.

Order-0 outsiders of v leave v in one of two ways:
* up, through v's fringe, which has bandwidth δ_F·π(v)/2 ≈ δ_F(ν²/(2k))·c(u) per side;
* down into v's children as order-1 outsiders. That channel is capped at k·δμ·c(child)/μc(v) ≲ ν of
  the outsider budget, because δ < 1/(kA).

So in steady state **ε_B/2 ≲ δ_F·ν²/(2k)**, i.e. ε_B ≲ δ_F ν²/k. This holds for any bookkeeping on this
tree and flow table.

Locality does not change the count of order-0 outsiders. Their sibling distance is irrelevant: all of
them must leave through the parent. Tapering by sibling distance therefore gains nothing.

What can change is the gap between (ν/k)² and δ_F ν²/k:
* (4.3) costs a factor 2/(δ_F k), which is 1 today and 32 at δ_F = 1/2;
* δ_F itself costs a factor of up to ~16.

### 2.2 What locality does buy (proposed contract)

**Property B_loc.** For each of the k+1 cuts, the mass crossing it is < (ε_B/2)·a. The mass displaced
across two or more block boundaries is < ε₂·a, with ε₂ = O(k²·ln m/m) ≈ O(ε_B²).
* The Lean `onesAboveBottom` predicate is already per cut, so the first half is free.
* The ε₂ part is heuristic: Lemma-6.1-style counting with deviation m/k.

**Property F_loc.** Of the j ≤ δ_F|F| extreme keys, fewer than ε_F·j miss F, with δ_F ≈ 1/2. Misses
land only in B_1 (resp. B_k), up to ε₂.

With these contracts, the invariant becomes P_loc. It is P with separate per-side constants μ_L, μ_R,
plus the fact that order-≥1 outsiders below a child w belong only to the ranges of w±1. That fact holds
because they are near-boundary keys that entered through fringe failures or cut crossings.

Lemma 4.2's cumulative boundary error then only sees cross-boundary hiding. Wire counts per subtree are
exact (Lemma 3.1, p. 9), so a key of child j hidden in child j+2's subtree is needed to move the j/j+1
boundary. The (k−1)·sib multiplier becomes 2·sib + O(ε₂).

**Replacement conditions** (per side; heuristic):

* (L2) ε_B/2 + s·(ν/(2Ak)) + μ(1 + 2·sib(δ) + δA²k) ≤ μAν. Here s ∈ [0, 1] is the remaining
  slack fraction: 1 for equal blocks, ≈ 0 for non-uniform blocks.
* (L3) μ ≤ ν/(Ak²), only if the top-node rule is kept.
* (L4) μ ≤ ½·δ_F·(Aνk−1)/(A²k²), with δ_F ≈ 1/2.
* (L5) ε_F ≤ Aνδ − A²kδ², δkA < 1.
* (F) f = m·ν/(2Ak)·(1−1/(Aνk))/(1−1/(Ak)²) ≥ f_floor, with ε_F(f) = 1/(656·f) (two-round route).

The recurrence is the one in Lemmas 4.3/4.4, with ε_B a replaced by ε_B a/2 per side and (k−1) by 2.
To first order, the tolerance is then **ε_B ≈ δ_F ν²/k − (ν/Ak)·s**.

### 2.3 The slack is removable (plausible, unproved)

The drift exists because the fringe always takes child 1's smallest and child k's largest keys, while
the blocks are equal. Fix: give the end blocks size β − π/2 and the middle blocks c/k.

The children's down-flows then depend on their position (end or middle relative to each ancestor).
That makes the flow table deterministic but inhomogeneous. In steady state the ancestors hold exactly
those fringe keys, so per-child compositions match the blocks up to:
* outsiders (the μ term, already budgeted);
* sibling hiding;
* separator and fringe errors;
* row rounding of block sizes (O(1/m)).

To prove:
* an inhomogeneous Lemma 3.1 (wires below each node, now position-dependent);
* integrality of the new π, β;
* a two-sided (lower and upper) composition bound replacing Lemma 4.1.

This is a real rewrite of §3, but it involves no probability.

### 2.4 Removing (4.3)

Options:
* keep a sacrificial level above the top that accepts the top node's outsiders;
* or delay the top's descent until μ·c(α) < 1, which needs top nodes with capacity below 2k² and
  therefore uneven splits at the top.

Both change only O(1) stages, so the cost is in the additive constant. I could not close either one
here. Flagged as an **assumption**. For k ≤ 2/δ_F, (4.3) is not binding anyway.

## 3. Exchange-rate table

The model runs a continuous search over x = lg k, y = lg A, z = lg(1/ν) (grid 0.1). Then:
* m = max(bulk need, fringe need, (Ak)² from (5.1));
* bulk need: two rounds per BULK2 (calibrated: threshold 2^41.66 at ε = 1/59e6, matching BULK2);
* stage = 3·T(lg m), T(L) = L(L+1)/2;
* "win" = best integer (x,y,z) with the power-of-two window 3·T(⌈lg m⌉+1). This reproduces 1419 at
  (6,12,6).

Two-round separators, current F route (f ≥ 92160, ε_F = 1/(656f)):

| ε_B | variant | (k, A, ν) cont. | lg m [bulk, fringe] | stage | stages/bit | slope ideal | int (x,y,z): win |
|---|---|---|---|---|---|---|---|
| 2^-26 | V0 today | (64, 2896, 1/60) | 41.9 [41.9, 41.9] | 2699 | 0.494 | 1334 | (6,12,6): 1419 |
| 2^-20 | V0 | (34, 549, 1/12) | 35.3 [33.6, 35.3] | 1921 | 0.773 | 1486 | (5,10,4): 1667 |
| 2^-12 | V0 | (2, 20, 1/3.2) | 24.6 [22.4, 24.6] | 946 | 3.12 | 2949 | (1,5,2): 3402 |
| 2^-26 | S (slack 0 only) | (69, 104, 1/68) | 41.9 | 2699 | 0.344 | 928 | (6,7,6): 1025 |
| 2^-20 | S | (39, 23, 1/13) | 33.6 | 1746 | 0.500 | 872 | (5,6,4): 1040 |
| 2^-26 | L3 (loc., δ_F=½, no (4.3)) | (676, 338, 1/79) | 41.9 | 2699 | 0.301 | 811 | (10,8,6): 891 |
| 2^-20 | L3 | (97, 69, 1/21) | 34.6 [33.6, 34.6] | 1847 | 0.437 | 808 | (7,7,5): 889 |
| 2^-26 | L4 (L3 + slack 0) | (630, 137, 1/97) | 41.9 | 2699 | 0.267 | 721 | (9,8,7): 801 |
| 2^-20 | L4 | (97, 30, 1/26) | 33.7 | 1755 | 0.371 | **650** | (7,6,5): 783 |
| 2^-16 | L4 | (32, 13, 1/11) | 29.7 [28.0, 29.7] | 1371 | 0.497 | 681 | (5,5,4): 842 |
| 2^-12 | L4 | (15, 6, 1/4.9) | 26.4 [22.4, 26.4] | 1083 | 0.725 | 785 | (3,4,3): 1015 |
| 2^-8 | L4 | (5, 4, 1/2.8) | 23.5 [16.7, 23.5] | 864 | 1.30 | 1126 | (3,2,1): 1625 |

Same variants, if F were provable at fringes f ≥ 2^10 (hypothetical):

| ε_B | variant | slope ideal | int: win |
|---|---|---|---|
| 2^-26 / 2^-20 / 2^-16 / 2^-12 / 2^-8 | V0 | 1334 / 1304 / 1488 / 2166 / – | 1419 / 1498 / 1814 / 2700 |
| same | L2 (loc., δ_F=½, (4.3) kept) | 1225 / 1023 / 893 / 775 / 854 | 1378 / 1181 / 1116 / 1050 / 1328 |
| same | L3 | 811 / 702 / 647 / 647 / 854 | 891 / 810 / 756 / 800 / 1260 |
| same | L4 | 721 / 617 / 562 / **528** / 598 | 801 / 702 / 698 / 700 / 950 |

Single-term ablations from V0, best over ε (`exchange_rate.out`):

| ablation | slope ideal |
|---|---|
| none | 1322 |
| sibling term removed | 1292 |
| per-side B | 1289 |
| slack removed | **878** (ε = 2^-20, (x,y,z) = (5.4, 4.1, 3.5)) |

One-round separators are at least as good only with the optimistic fringe ε_F = 1/(2f). That is the
obstruction value, a necessary condition and far from proved. Under that assumption L4 gives
600 ideal / 744 win at ε = 2^-12, lg m ≈ 29.4. Treat it as an upper bound on what one round could do.

**Assumptions (loud).**
* (a) ε_F(f) = 1/(656f) is extrapolated from the single certified point f = 131040 (F2ROUND).
* (b) f_floor = 92160 is a limit of the proof route, not a theorem about the separator.
* (c) δ_F = 1/2 is unproved. The F2 proof uses 128/4095.
* (d) "slack 0" and "drop (4.3)" are redesigns (§2.3, §2.4), not lemmas.
* (e) Integrality and divisibility of a non-power-of-two flow table are ignored. The integer column
  allows only powers of two.
* (f) The root separator and final sorters are ignored; they add only constants.
* (g) With small A (Aν ≈ 1.5–2) the margin μ(Aν−1) is thin, so second-order terms not modelled could
  bite.

## 4. Simulation (`sim_locality.py`)

Setup: m = 1024, n = 1024, k = 8 bands of 128 rows; one and two rounds. The adversary is chosen after
σ: the backward closure of `docs/chvatal-fringe-obstruction.md`, aimed at one band boundary with reach
H = R + 2·(m/k) + 1.

| input | rounds | misplaced mass | distance ≥ 2 | max \|displacement\| (rows) |
|---|---|---|---|---|
| random | 1 | 1.5e-2 | 0 | 13 |
| adversary | 1 | 3.5–4.7e-2 | **2.6–4.0e-4** (≈270–420 keys) | **≈300 > band 128** |
| random | 2 | 6.3e-3 | 0 | 6 |
| one-round adversary | 2 | 1.0–1.2e-2 | 0 | 12 |

At m = 4096 (n = 512, k = 16) random inputs again give no distance-≥2 keys (max displacement 20 vs
band 256).

Conclusions:
* **"Adjacent only" is false per key for one round.** An adversary that knows σ can push about one
  column's worth of keys (~m/k each) arbitrarily far. In mass it is ~1 % of the misplacement and
  O(1/m), so a contract must carry an ε₂ = O(1/m) term rather than assume zero.
* For two rounds, the one-round adversary produces nothing at distance ≥ 2. A genuine two-round
  pullback was not tested; the obstruction note suggests it costs a factor of ~2f more mass.

Fringe test (f = 32 rows, j = δ_F·f·n):

| | δ_F = 128/4095 | δ_F = 1/2 | δ_F = 0.9 |
|---|---|---|---|
| one round, random | 0 escapes | 0 | 10–15 |
| one round, adversarial | 0 | **297 of 16k** | ~760 |
| two rounds, adversarial | 0 | 0 | 0–8 |

This weakly supports δ_F ≈ 1/2 for two rounds only.

## 5. What would have to be proved, in order of value

1. **Non-uniform block flow table (slack → 0).**
   * Alone: 1419 → ~1025 (windowed, integer (6,7,6), same separator).
   * Deterministic and plausible.
   * The best next step: re-derive Lemmas 3.1/4.1/4.2 for the inhomogeneous table and certify the
     residual slack is ≤ ~10 % (`slack_sensitivity.out`: 10 % residual already costs +150).
2. **Top-node redesign removing (4.3).** It is worth ~1.5× only together with δ_F ≈ 1/2.
3. **A two-round Property F with δ_F ≈ 1/2.** Simulation-supported; unproved.
4. Small-fringe F (f ~ 2^10) and per-side/adjacent bookkeeping: each is worth ~5–10 %.

Even with all of these, the model sits at ~650 ideal / ~700–780 windowed. "Few hundred" is not reached
in this family.


## Ordinary outsider transition prototype (October 12)

TaperedOrdinaryKernel.lean defines a candidate all-order outsider invariant and a typed ordinary transition interface. Its focused check passes: conditional on the kernel's local separator/routing fields, P(t) implies P(t+1). `TaperedOrdinaryKernel.tapered_child_send_bound_of_owned_cover` also derives the child-up contribution from P plus explicit wire-cover, child-register ownership, and capacity-ratio premises. These premises are not yet instantiated by the global integer schedule. Parent-send and fringe rank fields, frontier cases, and global P remain open. See OUTSIDER-TRANSITION-AUDIT.md for the field map. The current candidate constants come from SignedReserve.lean: mu=17/71565312, delta=1/2^25, epsB=1/2^21. Earlier high-risk calculations using the legacy constants were corrected in HIGH-RISK-945.md.

## Ordinary routed-placement bridge (October 12)

`RaggedTreeRoute.raggedTreePlacementStep` now turns the actual address-indexed wire routing into a `PlacementStep` register cover, provided the routed wire sets are transported through an injective wire-to-key map into the next placement. At interior nodes the source-classification theorem identifies the residual sender set exactly with the child up-ports. At terminal nodes, the current total destination keeps the terminal bag's own down-ports in the residual; their numerical error is not covered by the child-up estimate. The module passed a focused Lean 4.29.0-rc4 compile using the existing scratch dependency cache. This closes only the set ownership/coverage interface: it does not instantiate integer cardinalities, `badSend0`, `fringeSend`, or the frontier transitions. See `OUTSIDER-TRANSITION-AUDIT.md`.
## Symmetric fringe transfer checked (October 12)

`BaselineFringe.paddedPack2Net_fLow_baseline` now proves the low-side counterpart to `paddedPack2Net_fHigh_baseline`, and `TruncatedPaddedWitness.fLow_baseline` exposes it using the stored flipped truncated SR/R1/R2 certificates. The proof runs the full pack on the padded permutation, applies `physicalPack2Net_flip`, bounds the reversed high cohort by the baseline-row F2 argument, and transfers the event through the live-prefix restriction. Its key geometric premise is `(f+1)*columns <= u` (the protected fringe fits the actual suffix); unlike the high-side theorem, padding cannot help this inequality. Both `BaselineFringe` and `TruncatedPaddedProvider` pass focused Lean 4.29.0-rc4 checks. Matching this theorem to every active ragged slot and proving the premise from the global schedule remain open.
The low-fringe fit arithmetic is now also connected to the local signed-flow invariant: low_fringe_fits_of_scheduled_flow derives the required suffix size from a LocalIntegerFlow, C >= 2^34, |eta| <= 69, and the occupancy identity. The remaining work is to instantiate this flow and the padded witness for the same scheduled bag, then connect both fringe orientations to the ragged routed slots and prove arbitrary-stage input tails. The focused TruncatedPaddedProvider check passes; the full tapered package is not built.
Same-bag integration hit a scale obstruction. SameBagScale.lean kernel-checks that every k with 4*k+8 <= d gives a distinct active schedule stage at the lower frontier with reference capacity exactly 2^34; this is a linear-size family. The padded scramble witness requires a >= 2^38 because its certified rectangle uses at least 2^34 rows and 16 columns. Thus the existing witness cannot cover this family under the intended 69-wire occupancy invariant. The first-round concentration inequality itself turns on near 17.15 billion rows for E=38/10^6, so changing only the rectangle arithmetic is insufficient. See SAME-BAG-INTEGRATION-AUDIT.md.
The exact low-capacity family is in the ordinary interior band: SameBagScale.lean also proves candidateAlpha+2 <= candidateOmega for its stages. Therefore the 2^38 witness-size obstruction cannot be isolated to a frontier cleanup. No same-bag fringe-send theorem follows until the local separator provider works at these 2^34-scale registers or the ordinary kernel changes.

October 13: `InvariantInputTails.lean` kernel-checks that the all-order
outsider bound gives both external tails of any bag, and extends them to an
internal cut with an additive interval-distance term. This is useful as a
baseline but does not derive ordinary `hL`/`hR`: at the interior stage
`t=10,l=2`, a native child interval is `2^18` times the reference capacity,
so the one-bag outsider invariant alone permits all of a capacity-sized
register in that interval. The ordinary rank-tail gate must use global
descendant-mass and outside-spill accounting; see the final section of
`OUTSIDER-TRANSITION-AUDIT.md`.
Rate audit: within the current two-round inequalities, round one requires E >= sqrt(L/m), L=log(2(m+1))+1/2, while optimizing the round-two rate over lambda gives K <= delta^2/(4E). Thus m*K <= m^(3/2)*delta^2/(4*sqrt(L)); at m=2^30 and delta=2^-21 this is only about 0.43 versus L about 21.99. Retuning E and lambda cannot lower the row threshold by 16x; a stronger rate proof or different local construction is needed.
