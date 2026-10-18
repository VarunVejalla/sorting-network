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
   fringe" (`t sqrt(lam) ≲ f`), at the cost of a fringe-load factor `L ≤ 3` from sibling drift
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

**Drift of far outsiders.** A far-right outsider of `v_j` is larger than every key of `v_{j+1}`,
so phase 1 moves it to `v_{j+1}`'s top and phase 2 moves it on to `v_{j+2}`'s top. Interior
siblings receive at most two siblings' far loads; the rightmost receives at most three. Far
outsiders still leave through *some* sibling's fringe, and all siblings' fringes go to `u`, so
the flow is unchanged. The fringe rows of one sibling, however, may carry up to `L = 3` times
the per-node far load. Property F must hold for that combined extreme set. Because the
siblings' scrambles are independent, the combined column counts are a sum of independent
staircases: a fringe event at fraction `L delta_F`.

## 5. Conditions replacing (4.2)–(4.5)

Write `side = 1/2` (per-side accounting, as in the L-variants), `lam = side eps_B m/(A nu)` for
the spill per column, and `f = m nu/(2Ak)` for the fringe height.

* **(4.2-L)** Order-0 outsiders *other than spill* (`u`'s outsiders, sibling hiding, slack, and
  the separator's distance-2 spill `eps_2` that lateral repair cannot cancel) satisfy Chvatal's
  (4.2) with `eps_B` replaced by `eps_2`. Heuristically `eps_2 = O(eps_B^2)`
  (`../tapered/NOTES.md` §2.2, simulation only).
* **(4.4-L)** `L mu ≤ (delta_F/2)(A nu k - 1)/(A^2 k^2)`, with Property F certified at fraction
  `delta_F`, so each node may use `delta_F/L`.
* **(O)** Overflow fits the order-1 budget: `O_j/(side eps_B a(u)) ≤ eta`, where `eta` enters
  (4.5) as `eps_F/(A nu) + delta^2 A k/nu + eta side eps_B/(mu A^2 nu^2) ≤ delta`. A sufficient
  heuristic is `f ≥ t sqrt(lam)` with a tail factor `t` (Gaussian scale: `t ≈ 6–8`), that is,
  `m ≥ t^2 (2Ak/nu)^2 side eps_B/(A nu)`.
* **(4.3), (4.5)** As in Chvatal or the L-variant, with `mu` from (4.2-L) and (4.4-L).
* **Cost per stage**: `3 T(lg m) + 2 (lg m + 1)`.

**What (O) needs proved.** A worst-case tail bound for `sum_c (|p_c + far_c - q_c| - f)_+`. The
McDiarmid argument of LATERAL-LEMMA.md is far too weak for a rare-event sum (its deviation term
does not decrease with `f`). This needs an F2ROUND-style argument: counting inputs by their tops,
and Chernoff bounds over sets of overfull columns, applied to the difference of two independent
staircases. It is the natural joint form of UB-15 and UB-20.

## 6. Status

* §3 is a correction to this branch's earlier model results (README.md, `lateral_*_model.py`):
  the claimed 343 / 426 / 480–540 slopes do not follow.
* §4–§5 are a derivation sketch. Open points: the drift argument across both phases at the ends
  of a sibling family; the interaction of the separator's own fringe with spill occupying the top
  rows (far outsiders are larger than spill, so they keep the top `delta_F` share, but this needs
  checking against Property F's exact statement); and whether `eps_2 = O(eps_B^2)` holds in the
  worst case.
* Re-pricing with §5 is in `lateral_composed_model.py`.
