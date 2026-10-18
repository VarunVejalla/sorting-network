# Composing lateral repair with Chvatal's invariant

UB-20 · 2026-10-18 · Claude (Opus 5.5). **Claim level: derivation sketch, unaudited.** Page
references are to DCS-TR-294 (`docs/dcs-tr-294.pdf`, printed page numbers).

## Summary

1. **The cost model's lateral substitution was wrong.** `lateral_*_model.py` replaced `eps_B` by
   `rho*eps_B` in Chvatal's (4.2), which treats the post-repair residual as **order-0** error.
   With band merges, or merges that skip the fringe rows, the residual sits in the sibling's
   middle rows and is sent **down**, arriving at a grandchild as an **order-1** outsider. Its
   budget is condition (4.5), smaller by a factor of about `delta ≈ 1/(kA)`. At the model's
   reported optimum the residual exceeds that budget by about 36x (§3). The 480–540 figures in
   README.md are therefore withdrawn.
2. **Repaired design.** Merge *full* sorted columns. The residual then lands deterministically
   in the fringe rows of one sibling and goes **up** whenever it fits. Only the per-column
   overflow beyond the fringe height goes down. The governing condition changes from
   Chvatal's "the spill fits the fringe" (`lam ≲ delta_F f`) to "the per-column residual fits the
   fringe" (`t sqrt(lam) ≲ f`), at the cost of a fringe-load factor `L = 2` from sibling drift
   (§4).
3. §5 lists the resulting conditions, which replace (4.2)–(4.5) for the cost model.

## 1. Chvatal's argument, as used here

Nodes on level `i` at time `t` hold `a(i,t)` wires, with capacity `c(i,t) = N A^i nu^t /(A nu k)`
(p. 7). A node sends `pi(i,t)` wires to its parent and `beta(i,t)` to each child (p. 8). In the
interior, `pi/c = (A nu k - 1)/(A^2 k^2)` and `beta/c = (Ak - nu)/(A k^2)`.

An **outsider** at node `x` is a key not addressed below `x`; it has **order r** if it would
remain an outsider after moving `r` levels up (p. 10). The invariant is

> **P** (p. 10): every node on level `i` holds fewer than `mu delta^r c(i,t)` outsiders of order `r`.

Each step uses P at time `t` to prove it at `t+1` for a node `v` with parent `u`:

* **Lemma 4.2 (p. 11).** `u` sends `v` fewer than
  `(mu + (k-1) Delta_1/c + slack + eps_B) c(u)` keys not addressed below `v`. Here `mu c` is
  `u`'s own outsiders, `(k-1) Delta_1` is sibling hiding (Lemma 4.1), and `slack` is the
  block/boundary drift.
* **Lemma 4.3, (4.2) (p. 12).** Order-0 outsiders at `v` come from `u` (Lemma 4.2, divided by
  `A nu`) and from `v`'s children (order 1 there, `mu delta A k/nu`). Requiring the total to stay
  below `mu c(v)` gives (4.2).
* **Lemma 4.4, (4.3)–(4.5) (p. 13).** Order-`r` outsiders at `v` come from `u`'s order-`(r-1)`
  outsiders that miss `u`'s fringe, plus `v`'s children's order-`(r+1)`. Condition (4.4),
  `mu ≤ (delta_F/2)(A nu k - 1)/(A^2 k^2)`, makes every order-`(r-1)` outsider of `u` fit in
  the `delta_F` part of the fringe covered by Property F, so at most `eps_F` of them are sent
  down. That gives (4.5): `eps_F/(A nu) + delta^2 A k/nu ≤ delta`.

The **flux law** is (4.2) together with (4.4): `eps_B ≲ mu A nu ≲ delta_F nu^2/k`. The
separator's spill becomes order-0 outsiders of `v`, and all of them must leave through `v`'s
fringe.

## 2. The modified stage

At every stage, after every node runs its separator and before routing, run two lateral phases
on each family of siblings `v_1, ..., v_k` (children of one `u`): first the pairs `(v_1,v_2)`,
`(v_3,v_4)`, ..., then `(v_2,v_3)`, `(v_4,v_5)`, .... A lateral merge of `(v_j, v_{j+1})` pairs
column `c` of `v_j` with column `c` of `v_{j+1}`. Both are sorted, so a bitonic merge of depth
`lg(2m)` puts the `m` smallest keys in `v_j`'s column and the `m` largest in `v_{j+1}`'s. Total
depth is `2 lg(2m)` per stage. Column sortedness is preserved, so row positions keep their
meaning (top `f` rows = upper fringe, and so on).

**Spill.** At stage `t`, `u`'s separator places `P_j` keys above the cut `t_j` into block `j`
and `Q_j` keys below it into block `j+1`. At time `t+1` these are order-0 outsiders of `v_j` and
`v_{j+1}`, extreme within their bags: the largest of `v_j` and the smallest of `v_{j+1}`, apart
from far outsiders. At stage `t+1`, each sibling's two-round separator spreads them over its
columns with counts `p_c`, `q_c`. Their law is given by the staircase representation
(LATERAL-LEMMA.md, Lemma 1).

## 3. Why the earlier substitution is wrong

Suppose the merge excluded the fringe rows (band merging, or the "fringe-excluded" variant).
Then the residual `|p_c - q_c|` of each column stays in the merged middle segment. That
segment is routed to the sibling's children, so a key above `t_j` left in `v_j`'s middle goes to
`v_j`'s last child `w`. At `w` it is an order-1 outsider: it is not below `v_j` but is below `u`.
Lemma 4.4 for `r = 1` must then absorb it:

```text
eps_F/(A nu) + delta^2 A k/nu + rho * side * eps_B / (mu A^2 nu^2)  ≤  delta.
```

The new third term uses `c(w) = (A nu)^2 c(u)`, and all of one cut's residual on that side goes
to the single child `w`. At the model's best lateral point (L4', `delta_F = 1/5`,
`(x,y,z) = (4, 3.5, 3)`, `rho = 0.218`, `eps_B = 2^-12`): `mu ≈ 6.6e-5`, `delta < 1/(kA) ≈ 5.5e-3`,
and `rho side eps_B /(mu A^2 nu^2) ≈ 0.2`, about 36 times the whole budget `delta`. Putting `rho`
into (4.2) instead, as the model did, is not what Lemma 4.4 requires.

## 4. Full-column merges route the residual up

With a full-column merge, take one column of `v_j` and one of `v_{j+1}`. Let `p` and `far_R` be
`v_j`'s keys above `t_j` (spill, plus far-right outsiders addressed beyond `u`), and `q` the keys
of `v_{j+1}` below `t_j`. Then deterministically:

* **If `p + far_R ≥ q`:** `v_{j+1}` receives the `m` largest keys of the two columns, including
  every far-right outsider. `v_j` keeps exactly `p + far_R - q` keys above `t_j`, all at the top
  of its column.
* **Otherwise:** `v_{j+1}` keeps `q - p - far_R` keys below `t_j`, all at the bottom.

So the misplaced keys left by the merge sit in the extreme rows. Whenever the count is at most
the fringe height `f`, they are in the fringe and go **up** to `u` as order-0 outsiders, which
is the normal Chvatal flow. Only the **overflow**

```text
O_j = sum_c ( |p_c + far_c - q_c| - f )_+
```

goes down as order-1 error. That overflow is a far-tail event. The spill itself no longer has
to fit the fringe; only its per-column imbalance does.

**Drift of far outsiders.** A far-right outsider of `v_j` is larger
than every non-far key of `v_{j+1}`, so phase 1 moves it to `v_{j+1}`'s top and phase 2 moves it
on to `v_{j+2}`'s top. With `k` a power of two (even), every sibling, ends included, receives at
most `L = 2` siblings' far loads (checked by the reviewer's simulation of both phases; `L = 3`
occurs only for odd `k`). Far outsiders still leave through *some* sibling's fringe, and all
siblings' fringes go to `u`, so the flow is unchanged. The fringe rows of one sibling, however,
may carry up to `L = 2` times the per-node far load, so a per-column fringe statement must hold
for that combined extreme set. If each sibling index uses its own independent scramble, the
combined column counts are a sum of independent staircases, a fringe event at fraction
`L delta_F`. With one shared network the adversary can align the column sets row by row, and this
fails (open lemma 2, §6).

## 5. Conditions replacing (4.2)–(4.5)

Write `side = 1/2` (per-side accounting, as in the L-variants), `lam = side eps_B m/(A nu)` for
the spill per column, and `f = m nu/(2Ak)` for the fringe height.

* **(4.2-L)** Order-0 outsiders *other than spill* (`u`'s outsiders, sibling hiding, slack, and
  the separator's distance-2 spill `eps_2` that lateral repair cannot cancel) satisfy Chvatal's
  (4.2) with `eps_B` replaced by `eps_2`, in the exact form
  `eps_2 <= mu (A nu - 1) - slack - mu((k-1) sib + delta A^2 k)`. Heuristically
  `eps_2 = O(eps_B^2)` (`../tapered/NOTES.md` §2.2, simulation only).
* **(4.4-L)** `L mu ≤ (delta_F/2)(A nu k - 1)/(A^2 k^2)`, with the fringe statement certified at
  the combined fraction `delta_F`, so each node may use `delta_F/L`.
* **(4.5-L)** A child receives the fringe misses of up to `L` siblings' far loads:
  `L eps_F/(A nu) + delta^2 A k/nu + (overflow term) ≤ delta`.
* **(O-L)** The per-column residual must fit the fringe rows *together with* everything sharing
  them: up to `L` siblings' far loads, `u`'s residual outsiders, sibling hiding, the distance-2
  spill, and the drift mean `D/n` (net drift `D = P - Q` shifts each column's mean). A
  sufficient heuristic is `f - m (L mu + (3 mu + slack + eps_2)/(A nu)) ≥ t sqrt(2 lam)`, with a
  Gaussian tail factor `t ≈ 6–10`.
* **Top and small nodes.** A top node at descent (`pi = 0`) has no fringe, so residual cannot go
  up. At the model's design point a node of size `Ak^2/nu` holds only a few spill keys, so (4.3)
  cannot simply be dropped. Nodes whose size does not allow columns of height `m` (near
  `alpha(t)`, partial `omega(t)` nodes, the root) cannot satisfy (O-L). **Proposed handling:** sort
  every node with `a ≤ m^1.7` exactly. That costs `T(lg a) ≤ 3 T(lg m)`, so it fits inside the
  stage depth, and it creates no outsiders (the UB-22 idea). The induction then needs this case
  split stated.
* **Cost per stage**: `3 T(lg m) + 2 (lg m + 1)`.

## 6. Review (2026-10-18) and status

An independent reviewer (fresh context, primary source only) checked this note and
LATERAL-LEMMA.md. **Confirmed:** the summary of Chvatal's argument; §3's diagnosis and its 36x
figure (recomputed as 36.5; about 56 with (4.3) kept); the deterministic full-column case
analysis; the timing; and Lemma 1 and the concentration inequality of LATERAL-LEMMA.md (McDiarmid,
sampling without replacement).

**Fixed after review:** `L = 2` instead of 3; the factor `L` in (4.5); co-resident loads and the
drift mean in (O); the union count in LATERAL-LEMMA.md; the exact form of the flux law
(`eps_B <= mu (A nu - 1) - slack`, a factor of about 3.4 tighter than `mu A nu` at `A nu = 1.41`);
and a case split for top and small nodes (§5).

**Open lemmas, required before any coefficient is claimed:**

1. **Spill locality.** A full-column merge inserts keys below `t_j` into `v_j`. If such keys can
   lie anywhere in `I_j`, they shift `v_j`'s own internal cuts by up to
   `side eps_B a(v)/(A nu)` rows, which is far above the `O(eps_B^2)` budget of (4.2-L). Property
   B does not localize the spill. Needed: the spill across a cut lies within the top `X` ranks of
   `I_j`, with `X` below the width of `v_j`'s last child block. For sort-based separators this is
   plausible (spill keys sit near the cut row of their columns, and column profiles track global
   rank), but it must be proved for every input.
2. **Joint per-column fringe statement.** After merging, one column's fringe rows hold extreme
   keys from up to `L` siblings' separators. Property F is a set-level statement about one
   separator, and F2ROUND's proof does not transfer. Needed: a per-column overflow bound for a sum
   of staircases. This requires **distinct scrambles per sibling index**; with one shared network,
   an adversary can align column sets row by row.
3. **Restated invariant `P'`.** At time `t+1` the full spill is still present, so P fails for
   order 0. State `P' = P` plus a structured spill class (spill counts per cut, extreme within
   the node), and re-prove Lemmas 4.2–4.4 for the post-merge configuration, which is not itself a
   separator output.

Model consequences of the fixes are in `lateral_composed_model.py` (rows `comp2_*.out`). Every
figure there is conditional on the three open lemmas.
