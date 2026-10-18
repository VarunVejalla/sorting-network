# Open lemma 1: spill locality for lateral repair

UB-20 · 2026-10-18 · Claude (Opus 5.5). **Claim level: derivation sketch, unaudited.** It
extends `upper-bound/best/notes/two-round/BULK2.md` (cited below by section) and uses the
notation of COMPOSITION.md.

## Summary

* **Deterministic part (exact).** A full-column merge moves a key that stays in `v_j` up by
  exactly the number of received keys smaller than it. So `v_j`'s internal block boundaries are
  disturbed only by received keys ranked below them. If every received key lies within the top
  child's rank range of `v_j`, the only boundary that moves is the one between the top child block
  and the upper fringe, which is harmless.
* **Probabilistic part.** The number of spilled keys ranked at least `W` below the cut is a
  bulk excess at a **row margin** `d0 = W/n_u`. BULK2's two-round argument extends to a positive
  margin, but its union over all intermediate states leaves a **floor**: for every input, far
  spill is at most `(eta/2) m n` per side with `eta ≈ 2 ln(m+1)/m`, once
  `d0 ≥ 0.72 E1 m`. The floor does not shrink as the margin grows.
* **Consequence.** The same floor bounds the separator's provable distance-2 spill `eps_2`. At
  the model's design point (`m ≈ 2^17.6`), `2 ln(m+1)/m ≈ 1.3e-4`. That is not small against the
  order-0 budget, so the heuristic `eps_2 = eps_B^2` used in `lateral_composed_model.py` was
  optimistic. The model is re-run with this floor (§5).

## 1. Deterministic shift lemma

Column `c` of `v_j` is sorted, and the full-column merge with `v_{j+1}` removes the `p` largest
keys of `v_j`'s column and inserts `q` keys from `v_{j+1}`, keeping `m` keys in sorted order. For
a key `x` that stays in `v_j`,

```text
new row(x) - old row(x) = #{ received keys smaller than x }      (rows counted from the bottom).
```

The removed keys are larger than every key that stays, so they do not affect `x`. Hence:

* keys below every received key keep their rows;
* a received key inserted below the row boundary between `v_j`'s blocks `B_{b}` and `B_{b+1}`
  moves exactly one key across that boundary, from `B_b` into `B_{b+1}`;
* if every received key ranks within `v_j`'s top child range `[t_j - W, t_j)`, only the boundary
  between `B_k` and the upper fringe moves. Keys pushed across it go up to `u`, which is always
  allowed, or down to child `k`, whose range contains them. No outsider is created.

So the only damage comes from **far received keys**, ranked below `t_j - W`. Each one causes at
most one wrong key at each internal boundary above it. That wrong key is a key of child `b` sent
to child `b+1`: an order-0 outsider at that grandchild-level node, charged to `v_j`'s own
(4.2-L) budget.

Here `W` is the rank width of one child of `v_j`, about `|I_j|/k ≈ a(u)/k^2`, so in `u`'s rows
the margin is `d0 = W/n_u ≈ m/k^2`.

## 2. Far spill is a bulk excess at a margin

In `u`'s separator output, let the cut between blocks `j` and `j+1` be row `i` (in BULK2's
bottom-counted convention). Take the threshold set of keys ranked below `t_j - W`. Its mass is
`n(i - d0)` exactly. Received keys ranked below `t_j - W` are exactly the members of this set
that end in rows `≥ i`, so

```text
far spill = onesAboveBottom(c', sigma2, i) = sum_j ( final_j - i )_+   with  sum_j final_j = n (i - d0).
```

This is BULK2's round-2 quantity, but evaluated at a row that sits `d0` above the set's mean.

## 3. Extending BULK2 to a margin

Follow BULK2 §2 with the state `c'` (round-1 output column sums for this threshold), exact mass
`n i'`, `i' = i - d0`.

* **Variance (BULK2 (c)).** At exact mass `i'`, `V = sum_r p_r(1-p_r) <= 2 exc(c', i')/n < E1 m`,
  using the round-1 predicate at threshold `i'`. BULK2's round-1 predicate covers every `i`, so
  this is available.
* **Tail (BULK2 (d)–(e)).** If far spill is at least `T`, the excess column set `S` (`|S| = s`)
  has `Y >= s i + T`, while `E Y = s i'`. The same Bernoulli MGF bound gives

  ```text
  fraction of bad sigma2  <=  exp( -lam T - s (lam d0 - c(lam) E1 m) ),   0 <= lam <= 1,
  c(lam) = lam^2 (1/2 + 2 lam/9).
  ```

  The margin contributes `-lam d0` **per overfull column**. Once `lam d0 >= c(lam) E1 m`, it can
  only help.
* **Union (BULK2 (f)).** Over `(c', S) in (m+1)^n x 2^n`. The `2^n` factor is harmless once the
  per-column exponent is negative, but the `(m+1)^n` states cost `n ln(m+1)`, and only `lam T`
  can pay it. With `lam = 1`:

  ```text
  T >= n ln(m+1) + O(ln n)     i.e.   far spill <= (eta/2) m n,   eta = 2 ln(m+1)/m (1 + o(1)),
  valid when  d0 >= c(1) E1 m = 0.722 E1 m,  E1 = sqrt(2 (1 + ln m)/m).
  ```

So, for every input, keys spill past the cut by more than `d0` rows only in a mass that is at
most a floor, set by the input entropy, not by the margin. The ruled-out list records the same
entropy as the source of the `ln m` in Property B's own `eps_B` (`backlog/ruled-out.md`, first
item).

**Margin condition.** With `d0 = m/k^2` (shift) or `m/k` (distance 2), `d0 >= 0.722 E1 m` needs
`m >= 1.04 k^4 (1 + ln m)` for the shift case: about `2^15.8` at `k = 8`.

## 4. What this costs

The floor enters twice, per side and per cut, in Chvatal's units (fraction of `u`'s wires):

* **Distance-2 spill** (margin `m/k`): `eps_2 <= eta`. Previously modeled as `eps_B^2`, which is
  smaller at the design point (`eps_B = 2^-8.5` gives `eps_B^2 ≈ 7.6e-6` against `eta ≈ 1.3e-4`).
* **Shift errors at `v_j`'s internal cuts** (margin `m/k^2`): at most `(eta/2) a(u)` per boundary,
  that is `eta/(A nu)` in the per-side units of `v`'s budget.

Together they replace the heuristic in (4.2-L): `eps_2,eff = kappa * 2 ln(m+1)/m` with
`kappa ≈ 1 + 1/(A nu) ≈ 1.7`.

## 5. Model consequence

`lateral_composed_model.py` with `EPS2_FLOOR=kappa` uses `eps_2 = kappa 2 ln(m+1)/m`, iterated to
a fixed point in `m`, plus the margin condition `m >= 1.04 k^4 (1 + ln m)`. Results are in
`comp3_*.out` and README.md.

## 6. Limits of this sketch

* The floor is a property of the union-bound proof, not necessarily of the separator. A proof
  that counts only states reachable after round 1, or exploits round 1's randomness jointly
  (the `h^2/2` adversary cost), might lower it. That is the same open question as tightening
  Property B's own `ln m`.
* The BULK2 extension reuses its lemmas unchanged except for the margin term; the exact-mass
  hypothesis holds because the threshold is a rank cut. This should be re-checked against
  BULK2's Lean-facing statements.
* The derivation treats one cut and one orientation; both orientations and all `k+1` cuts of
  `u` need the usual union (a factor `2(k+1)`, which is negligible).

## 7. Review (2026-10-18) and corrections

An independent reviewer checked this note against BULK2.md and DCS-TR-294. **Confirmed:** the
shift identity (rows counted from the bottom, `v_j` keeps the `m` smallest); the tail exponent of
§3; the arithmetic of §3 (`c(1) = 13/18`, `2 c(1)^2 = 1.043`; the margin bound solves to
`m >= 2^15.63` at `k = 8`, not 2^15.8); and the units in §4 (`kappa = 1 + 1/(A nu) ≈ 1.71`, under a
uniform-level assumption that should be stated).

**Corrections:**

1. **The margin in §1–§2 was unjustified.** What enters BULK2 is the number of *`u`'s* keys
   ranked in `v_j`'s top-child range, divided by `n_u`. P controls only outsiders, so nothing
   bounds how `u`'s keys in `I_j` spread over `v_j`'s children. The step `|I_j|/k ≈ a(u)/k^2`
   confused a block size with an address width. **Replacement argument (to be checked):** at
   every stage `u` receives `v_j`'s previous upper fringe, `v_j`'s `pi(v)/2` largest keys. By
   (4.4) at most a `delta_F` share of them are outsiders. `v_j` holds about `c(v)/k ≫ pi(v)/2`
   keys of its top child (keys addressed below a child, minus the few wires in ancestors), so the
   rest lie in the top-child range. That gives a margin in `u`'s rows of

   ```text
   d0_sh ≥ m [ (1 - delta_F) (A nu k - 1) A nu / (2 A^2 k^2)  -  D/c(u) ],   D/c(u) ≈ 3 mu + slack,
   ```

   about `nu^2 k/2` times the earlier `m/k^2`. The distance-2 case keeps its block-level margin
   `m/k`, which Lemma 4.2's count of `u`'s keys in `I_j` does control.
2. **The floor is not independent of the margin.** It came from capping `lam ≤ 1` in BULK2's
   lemma (d). Bennett's bound `E e^{lam(X - p)} <= exp(p(1-p)(e^lam - 1 - lam))` holds for every
   `lam ≥ 0`, and so does `avg_exp_hit_le`. With `R = d0/(E1 m)` and `lam*` the largest `lam` with
   `(e^lam - 1 - lam)/lam <= R`, the floor is `T = n ln(2(m+1))/lam*`. It shrinks like `1/ln R`.
   Counting only admissible states (an `l1` ball of radius `E1 mn`) replaces `ln(2(m+1))` per
   column by about `1 + ln(1 + E1 m) + ln 2`. The hard margin condition is gone: a smaller margin
   simply gives a larger floor. The union also carries `ln 2` per column from the `2^n` subsets,
   so the floor is `n ln(2(m+1))`.
3. **§1's "only the top boundary moves" conflated rank with row.** A received key ranked in
   child `k`'s range can still be inserted below the `B_{k-1}/B_k` row boundary, because `v_j`'s
   own separator is imperfect. The conclusion survives: every displaced key `x` is larger than
   the received key `y`, so `x ≥ t_j - W` and pushing `x` up creates no outsider. Sharp form: the
   number of wrong keys at boundary `b` is at most the number of received keys ranked below the
   lower end `L_{b+1}` of child `b+1`'s range.
4. **§2's identification is an upper bound, not "exactly".** It also misses keys that `v_{j+1}`
   received from its own children (order-0 outsiders there, ranked below `t_j`) and keys relayed
   from `v_{j+2}` through phase 1. Their count is bounded by the children-inflow term of (4.2),
   `mu delta A k/nu c(v)`. The model therefore doubles that term.
5. **Two phases and mirror orientation.** Displacements from the two phases compose (up by keys
   received below, then down by keys received above), so per-boundary bounds are summed over both
   phases. Keys received from `v_{j-1}` ranked above `t_{j-1} + W`, including drifting far-right
   outsiders, push keys *down*. This is the mirror case and needs the same lemma written out.
6. **Fringe boundaries.** Keys pushed from `v_j`'s fringe into `B_1` or `B_k` that are `v_j`'s
   own outsiders become order-1 outsiders at a child (the (4.5) budget). The model's overflow
   condition (O-L) requires the fringe rows to hold everything that must go up, including the
   co-resident loads, which covers this case. The written argument still has to say so.
7. **Still open:** unequal sibling sizes (partial and `omega` nodes change `W` and `m`); the
   integer form of the exact-mass step (`n(i - d0)` need not be a multiple of `n`; rounding costs
   at most `n` in `exc`); and the union over cut positions (harmless).

Model with these corrections: `lateral_floor_model2.py`, output `comp4_*.out`.
