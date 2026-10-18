# Open lemmas 2 and 3: joint fringe bound and restated invariant

UB-20 · 2026-10-18 · Claude (Opus 5.5). **Claim level: sketch, unaudited.** Notation follows
COMPOSITION.md and SPILL-LOCALITY.md. Page references are to DCS-TR-294.

## Lemma 2: joint per-column fringe bound

### Setting

After the two merge phases, the fringe rows of one column `c` of a sibling `v` hold:

* far loads (extreme keys that must go up) from at most `L = 2` siblings' separators (`v` and the
  one or two siblings whose far loads drifted to it, COMPOSITION.md §4);
* the merge residual `|p_c + far_c - q_c|` at `v`'s boundary with the merge partner;
* co-resident order-0 keys: `u`'s residual outsiders, sibling hiding, distance-2 spill, and the
  drift mean `D/n`.

What must hold, for every input, is a per-column overflow bound:

```text
sum_c ( farload_c + resid_c + other_c - f )_+  <=  eta_O * a(u)      (to be charged to (4.5)).
```

### Structural requirement: one scramble per sibling index

Each sibling index `s = 1..k` uses its **own** independent round-2 scramble `sigma2^(s)` (and its
own `sigma1^(s)`). This is the reviewer's condition. With one shared network an adversary can
align the column sets of different siblings row by row, and the counts then add linearly.

The cost is existence only: the union bound now has to hold for `k` independent scrambles
instead of one. The existing pigeonhole (`exists_and_flip`) extends to the product, and the
failure budget gains a factor `k`, which is negligible against `e^-hundreds`.

### Far loads: a sum of staircases is a staircase

By the staircase lemma (LATERAL-LEMMA.md, Lemma 1), sibling `s`'s extreme-set count in column `c`
is `sum_i X^(s)_{i,c}`, where each row `i` contributes an independent uniform `a^(s)_i`-subset.
Rows of different siblings are independent because their scrambles are. So

```text
farload_c = sum_{s in S_c} sum_i X^(s)_{i,c}
```

is again a sum of independent row-subsets, over the **virtual matrix** formed by stacking the
`<= L` siblings' rows (`<= L m` rows, combined profile `(a^(s)_i)_{s,i}`). F2ROUND's argument
uses only this row structure and the counts of profiles. Its R1 conditions (round 1, per sibling)
are unchanged. Its R2 condition becomes a statement about the virtual matrix with

* support `kappa -> L kappa` and mass `B -> L B` (each sibling contributes its own truncated
  heights `y^(s)`),
* the profile count raised to the `L`-th power (`ln Y -> L ln Y`).

That is exactly a single-separator fringe event at fraction `L delta_F` with `L`-fold entropy,
which is how `lateral_floor_model2.py` already charges it: Property F certified at `delta_F` for
the combined set, each node using `delta_F / L`.

### Residual: a signed staircase

`resid_c = |p_c - q_c|` (plus far terms) is the absolute value of a difference of two independent
staircases, from `v_j`'s and `v_{j+1}`'s scrambles. Per column, `p_c - q_c` is a sum of
independent `{0, +1}` and `{0, -1}` row indicators, so Bernstein's inequality applies per column.
The rare-event sum over columns needs F2ROUND's structure again, with the R2 union over pairs of
truncated profiles and a Chernoff bound over sets `S` of overfull columns. The mean is zero
except for the drift `D/n`, which is why (O-L) subtracts `D/n` from the fringe height.

**Sketch-level conclusion.** (O-L) is an R2-type event over `2 + L` independent staircases with
the fringe height reduced by the co-resident loads. The model's heuristic `t sqrt(2 lam)` slack
stands in for the certified version of that event. **To do:** extend `fringe_general_screen.py`
to the virtual-matrix R2 with signed rows, and replace `t` by the certified slack.

## Lemma 3: the restated invariant P'

### Why P fails

At time `t+1`, a node `v` holds the fresh spill from `u`'s stage-`t` separator, about
`side eps_B a(u)` per cut-side. That exceeds `mu c(v)` by design (lateral repair is meant to
allow `eps_B ≫ mu A nu`), so P's order-0 clause fails.

### P'

At every time `t` and node `x` on level `i`:

* **(P'_r), r ≥ 1:** fewer than `mu delta^r c(i,t)` outsiders of order `r` (as in P).
* **(P'_0 far):** fewer than `mu c(i,t)` order-0 outsiders **other than fresh spill**.
* **(P'_0 spill):** the fresh spill of `x` consists of at most `S_R(x)` keys addressed below `x`'s
  right sibling and `S_L(x)` addressed below its left sibling. They arrived in `x`'s block at
  time `t`, by definition lie above (resp. below) every key addressed below `x`, and satisfy
  `S_R(x_j) - S_L(x_{j+1}) = D_j`, the net drift at the cut, with `|D_j| <= D_max c(u)`.

The spill bound itself is Property B of `u`'s separator: `S_R, S_L <= side eps_B a(u)`.

### One stage, `t -> t+1`

Order of operations: every node runs its separator; then two merge phases among each sibling
family; then routing (fringes up, blocks down). Small nodes (`a <= m^1.7`) instead sort exactly and
create no outsiders.

1. **Merges consume the spill.** At stage `t+1` the merge between `v_j` and `v_{j+1}` cancels
   their spill classes up to the residual. With (O-L), the residual is in fringe rows and goes up
   to `u`, where it is not an outsider. Only the overflow goes down. So after the merges, no
   fresh spill remains outside fringe rows except overflow `<= eta_O a(u)`. (Uses Lemma 2.)
2. **Lemma 4.1 (p. 11)** is unchanged. It uses only odd orders `>= 1` in subtrees (`P'_r`) and
   Lemma 3.1's wire counts, which merges do not change.
3. **Lemma 4.2' (u's blocks).** Keys of `u`'s post-merge block `B_j` not addressed below child
   `j` number fewer than

   ```text
   [ mu + (k-1) Delta_1/c + slack + side (eta_d2 + eta_sh) ] c(u)  +  overflow,
   ```

   where `mu c` is `u`'s far order-0 outsiders (`P'_0 far`; drifted far keys stay in fringe rows
   by (O-L)), `eta_d2` is the distance-2 spill and `eta_sh` the shift damage at `u`'s internal
   cuts (SPILL-LOCALITY.md). The separator's adjacent spill `side eps_B a(u)` is **not** in this
   count: it becomes `v_j`'s spill class.
4. **Lemma 4.3' (order 0 at `v`, time `t+1`).** The far part comes from item 3 (divided by
   `A nu`), from `v`'s children's order-1 outsiders (`mu delta A k / nu`), and from the
   children-inflow keys relayed by `v`'s merge partner (another `mu delta A k / nu`, review item
   A4). Requiring `< mu c(v)` gives (4.2-L) as implemented in `lateral_floor_model2.py`
   (`2 delta A^2 k` term). The spill part is Property B of `u`.
5. **Lemma 4.4' (order `r >= 1` at `v`).** Sources are `u`'s order-`(r-1)` outsiders that miss
   `u`'s fringe and `v`'s children's order-`(r+1)` outsiders. For `r = 1` the first source is
   `u`'s far order-0 outsiders, at most `L` loads in one fringe, giving `L eps_F` escapes, plus
   `u`'s overflow. This gives (4.5-L): `L eps_F/(A nu) + eta_O/(mu (A nu)^2) + delta^2 A k/nu <=
   delta`. For `r >= 2` the far loads again carry the factor `L`. (4.4-L) makes the far loads fit
   the `delta_F`-share of the fringe.
6. **Top and small nodes.** Nodes with `a <= m^1.7` sort exactly. In particular the descending
   top node, with `pi = 0`, holds no outsiders afterwards, which replaces Chvatal's (4.3). Exact
   sorting costs `T(lg a) <= 3 T(lg m)`, inside the stage depth. A node that sorts exactly sends
   correctly ranked blocks, so its children receive no fresh spill; the merge at its children's
   level then has `P = Q = 0`.
7. **Terminal condition** (Lemma 4.5): unchanged. Spill classes are empty once all active nodes
   are small enough to sort exactly.

### Gaps in this sketch

* **Item 1 assumes the spill is extreme in both siblings.** That holds by definition for keys
  addressed to an adjacent sibling, but the residual computation also includes `v`'s far keys
  (`far_c`) and relayed keys. Their effect is bounded in (O-L) only heuristically.
* **Item 3 uses "drifted far keys stay in fringe rows".** It needs (O-L) at the receiving sibling
  *after both phases*, not just one.
* **Unequal sibling sizes** (partial `omega` nodes, non-uniform flow table at the ends) change `m`,
  `W` and the column pairing. Pair `min(n_j, n_{j+1})` columns and charge the unpaired spill to
  item 3.
* **The root and the first stages** (Chvatal's (4.1), `eps* <= mu/k`) are unchanged; the root's
  children have no spill class at `t = 1` beyond `eps*`.

## Review (2026-10-18): not a valid sketch; route parked

An independent reviewer found:

1. **(O-L) cannot be proved this way.** The spill per column is `lam ≈ 4–8e4`, far above
   `f ≈ 2.4–3.4e3`, so F2ROUND's truncated machinery does not apply to the residual. Bennett plus
   a union over states leaves an overflow floor of about `1–3e-4` against a (4.5-L) budget of about
   `1e-7–1e-6`, 100–500x over. The model's `t sqrt(2 lam)` had no entropy term, and its (4.5-L) had
   no overflow term. **This is decisive; see VERDICT.md.**
2. **Item 6 is wrong.** Exact sorting does not remove outsiders already in a node, so (4.3) is
   still needed. Exact sorting also creates cut-drift misplacement, so "P = Q = 0" is false.
3. **The far-load transfer to F2ROUND is wrong as stated.** The stacked matrix's trivial baseline
   `L g2 > f` makes `Phi < 0`. Fix: the deterministic split
   `(sum_s w_s - f)_+ <= sum_s (w_s - f/L)_+`, with per-sibling F at height `f/L`. This needs no
   independent scrambles.
4. **P' is inconsistent.** The spill bound and `S_R - S_L = D_j` conflict as `eps_B -> 0`.
   `D_j` must be bounded separately by `mu c + max(j, k-j) Delta_1 + slack`. "Fresh spill" should
   be defined by counts. `side = 1/2` needs a per-threshold Property B.
5. Items 1, 2, 4, 5 and 7 are correct or conservative modulo wording. The doc's "one or two
   siblings" contradicts `L = 2`.
