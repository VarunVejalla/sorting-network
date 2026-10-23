# Proof sketches for L3 (far crossings) and L4 (prefix sidedness) (2026-10-22)

Claude (Opus 5.5). **Claim level: proof sketches, unreviewed.** These are the two lemmas new in
`INDUCTION-v6.md`. R1 refers to `../../best/notes/sub800/R1-PROOF.md`.

## L4. Prefix sidedness (count form)

**Setting.** Node u, with `range(u)` an interval of ranks. Let `Anc(u)` be the keys of range(u) located
strictly above u (at an ancestor), and `Lat(u)` the keys of range(u) located in a non-ancestor outside
subtree(u). Write `Anc_L(u)` / `Anc_H(u)` for the parts of `Anc(u)` that entered the ancestors through an
F₁ / F₂ block.

**Claim.** At every time, `Anc_L(u)` consists of the `|Anc_L(u)|` **lowest** keys of range(u), except for
at most `X_L(u)` keys. Here `X_L(u)` counts the separator crossings and far moves charged in the
certificate along the path. Symmetrically for H. Moreover `|Anc_L(u)| = G_L(u) ± X_L(u)`, with `G_L` the
design quantity of §2 (`G_L += π/2` at each send of u; inherited θ at the parent's sends).

**Proof sketch** (induction on time t). Keys of range(u) can sit above u only if they were sent up by u
or by some node on the path from u to the top, or never sent down by an ancestor.
1. **Sent up by u.** u's F₁ holds the π/2 lowest keys of u's bag (exact sort; separators add crossings).
   * u's bag holds, in rank order: its low outsiders `O_L`, then keys of range(u) by rank.
   * By the induction hypothesis, range(u)'s lowest `|Anc_L(u)|` keys are not in u's bag (they are above).
     So the keys of range(u) that go up are the **next** lowest ones: `π/2 − O_L` keys starting just
     above `Anc_L(u)`.
   * Hence `Anc_L` stays a lowest segment and grows by `π/2 − O_L`. The design adds `π/2`, and the
     difference `O_L` is part of `N_L` (centred, §3 of v6). That is the "±" in the count.
2. **Not sent down by the parent p.** p's bag holds `Anc_L(u) ∩ (p's bag)` together with other keys.
   * If u is p's end-low child, then range(u)'s lowest keys are p's lowest own keys. p's F₁ sends up the
     lowest `π/2 − O_L(p)` of them, still a lowest segment by the same argument.
   * Those of range(u) that p sends to u's block return to u, and `Anc_L(u)` shrinks from its **top**.
     It stays a lowest segment, because p's block for u starts at a fixed position and the keys below
     that position are p's F₁ keys, lower in rank.
   * If u is interior for p, p's F blocks contain no keys of range(u), except through crossings (counted)
     or when p's prefix spills into u. In the spill case u is a prefix child of p, and the lowest keys of
     range(u) go up first by the same rank argument.
3. **Lateral keys** `Lat(u)` arise only from p's boundary shift and crossings, at u's lowest or highest
   keys (shift), or anywhere (crossings, counted). They are in the certificate's `N_L` and crossing terms,
   not in `Anc`.

**Consequence (L4).** Since `Anc_L(u)` is a lowest segment of range(u) of size `G_L(u) ± X_L`, and the
spill rule assigns `θ_low = π/2 + G_L(u) + o` to children in rank order, capping each at its deficit, the
children that receive low deficit are exactly a low prefix. Their ancestral keys are the lowest keys of
their own ranges. ∎ (sketch)

**What a full proof must make precise:**
1. that "the keys below p's block for u are lower in rank" holds with separators. This holds up to the
   crossings L2/L3 count;
2. the topRise/topDesc oscillation: when the top level moves, top nodes have `Anc = ∅` (G = 0);
3. the meeting of the low and high prefixes at sparse nodes (charged as spill).

## L3. Far crossings at a margin

**Setting.** Sender u, end child `w = w_1`, and `w_1′` = the first child of w. In u's bag, `Y` keys belong
to range(`w_1′`). The output positions are F₁ (`π/2`), then `B₁` (`b₁`), …

**Claim.** The number of keys that cross the F₁|B₁ position cut **upward** from rank at least
`π/2 + (Y − π/2)` (i.e. keys of range(w) above range(`w_1′`) landing in F₁) is at most `T(dB·m)·a`. Here
`dB·a = Y − π/2`, and `T(r)` is the walk-bound tail of round-1 excess beyond a margin of r rows. The same
holds at B₁|B₂ for w's own keys leaving downward-to-upward over `dL·a = b₁ + π/2 − Y` ranks.

**Proof sketch.**
1. **Reduction to a threshold.** Consider the threshold set of the `π/2 + (Y − π/2) = Y` lowest keys of
   u's bag. A key of rank `≥ Y` lands in F₁ (positions `< π/2`) only if, in the separator's output, fewer
   than `π/2` of the threshold keys occupy positions below `π/2`. Equivalently, the threshold set's
   "excess beyond position `π/2`" is at least `Y − π/2 + 1` keys **in the positions it should have
   filled**.
2. **Rows.** In the `m × n` layout, a threshold of `T` keys whose sorted positions end at row `T/n`, with
   the cut at row `(π/2)/n`, has a margin of `(Y − π/2)/n = dB·a/n = dB·m` rows (`a = mn`). A cross of
   that distance requires the threshold's column counts after round 1 to deviate by more than `dB·m` rows
   in the relevant columns. That is round-1 excess beyond the margin: `Σ_u (z_u − b − dB·m)₊`, with b the
   threshold's mean row.
3. **Two-round separator** (sort, scramble, sort, scramble, sort): the final position of a key is
   determined by round-2 loads, which are bounded by round-1 sources. A key lands more than `dB·m` rows
   from its rank row only if its round-1 source column is more than `dB·m` rows off (the band-adversary
   analysis, `band_adversary.py`, and the walk-bound margin version). So the count is at most the
   walk-bound tail `T(dB·m)·mn`.
4. **Band repair** (third sort replaced by sorts of disjoint bands of `2W` rows). Keys within the band
   containing their rank row end exactly. A key displaced across a band boundary moves at most one band.
   With `2W ≤ dB·m`, a crossing over `dB·m` rows still needs round-1 excess beyond about `dB·m − 2W`. The
   review requires the disjoint form, and the margin `dB·m − 2W ≥ dB·m/2` (`W ≤ dB·m/4`) costs a factor 2
   in the tail argument. At (4,4,3), q = 24: `dL ≥ 0.026`, so `dL·m ≈ 4.4e5` rows, while `2W ≈ 2^18.4` rows
   by the band's room. So the margin is about `1.0e5` rows, and the tail stays `≤ 1e-6`.
5. **One tail per side**, so the total is `≤ T(dB·m) + T(dL·m)` per end child (review D). ∎ (sketch)

**What a full proof must make precise:**
* the margin version of the walk bound (ROUND2/WALK-BOUND with an excess threshold shifted by `d·m`
  rows). SPILL-LOCALITY.md §3 extends BULK2 to a margin, but with a union floor. The energy method would
  replace that floor; its dense-regime evaluator is in `../fringe-duality/route_d_rigorous.py`;
* the band-repair displacement bound at the actual band geometry.

---

## L3, full proof under band repair (2026-10-22, replaces steps 2 – 4 of the sketch)

**Separator.** u's bag of `a = mn` keys sits in an `m × n` matrix, with rows counted from the bottom and
output position `r·n + j`. The stage is:
* `S1` (sort every column);
* `σ1` (row scramble: each row's entries permuted among the columns);
* `S2` (sort columns);
* `σ2` (row scramble);
* `Band`: for each output cut at row i, sort each column's segment `Seg(i) = [i − W, i + W) ∩ [0, m)`.

Cuts are at least 2W rows apart (interior blocks are about `m/k = 2^20` rows; `2W = 2^18`), so the
segments are disjoint. Cuts at fractional rows round to whole rows. That costs at most n keys per cut,
inside ROUND (`n/a = 1/m`).

**Notation.** For a threshold set X (the `|X|` lowest keys of the bag), `c′_k` is X's count in column k
after `S2`. The round-1 margin excess and deficit are

    E⁺(h) = Σ_k (c′_k − h)₊,   E⁻(h) = Σ_k (h − c′_k)₊.

**Row identity.** σ2 permutes entries within rows. After `S2`, column k holds X exactly in rows `< c′_k`.
So after σ2, row r holds `#{k : c′_k > r}` X-keys, and **rows ≥ h hold exactly `E⁺(h)` X-keys and rows
< h exactly `E⁻(h)` non-X keys**. Band moves keys only within their own segment.

**Lemma L3a (far crossings).** Let `|X| = n(i − d₀)` with `d₀ ≥ 0`, and let i be a cut. Then the number of
X-keys at rows ≥ i after Band is **at most `E⁺(i − W)`**.

*Proof.* An X-key at row ≥ i after Band either
* lies at row `≥ i + W`, outside every segment that reaches below `i + W`, so it was there after σ2; or
* lies in `Seg(i)`, whose rows are all `≥ i − W`, so it was in that segment after σ2.

Segments of other cuts lie entirely above `i + W` or below `i − W`, and keys never leave their segment.
So every such key was at row `≥ i − W` after σ2. There are `E⁺(i − W)` of them by the row identity. ∎

**Mirror.** For `|X| = n(i + d₀)`, the number of non-X keys at rows `< i` is at most `E⁻(i + W)`.

**Lemma L3b (band escapes at the cut itself).** Let `|X| = n·i`. Then the X-keys above row i after Band
number at most

    Σ_j (c″_j − i)₊ + E⁺(i + W) + E⁻(i − W),

where `c″_j` is X's count in column j after σ2 (BULK2's round-2 quantity).

*Proof.* In column j, let `L_j, B_j, U_j` be X's counts below, inside and above `Seg(i)` after σ2.
* Band sorts the segment, so X fills `[i − W, i − W + B_j)`. The keys above i number
  `U_j + (B_j − W)₊`.
* Since `c″_j = L_j + B_j + U_j`:
  `B_j − W = (c″_j − i) + (i − W − L_j) − U_j ≤ (c″_j − i)₊ + (i − W − L_j)`, with `i − W − L_j ≥ 0`.
* Summing over j:
  * `Σ U_j = E⁺(i + W)` (row identity, rows `≥ i + W`; U counts only those);
  * `Σ_j (i − W − L_j)` is the number of non-X keys in rows `< i − W`, which is `E⁻(i − W)`.

∎

**Bounds** (round 1 two-tailed, per cut, as fractions of `a = mn`):
* `E⁺(h)` and `E⁻(h)` at margin r rows from X's mean are at most the certified round-1 margin tail
  `T(r)` (`cert_walk_n.py tail`: `sup_p (φ₁(p) − r p)/m`; the p-cells cover both ends);
* `Σ_j (c″_j − i)₊ < (d/2)·mn` by BULK2's round-2 predicate (bulk precision `d`, `cert_walk_n8192.out`).

Hence:
* **Band escapes per cut ≤ `d/2 + 2·T(W)`**, two-sided: `d + 2T(W)` in the budget, as `screen.band` uses.
* **Far crossings at margin `d₀` ≤ `T(d₀ − W)`** for `d₀ ≥ W`. `width_sim` uses `T(d₀ − 2W)`, which is
  conservative (T is decreasing), and Property B when `d₀ − 2W < 0.005 m`.

**What changed against the sketch.**
1. No round-2 non-amplification step is needed. The far-crossing count is a round-1 quantity
   **deterministically**, because σ2 preserves row counts and Band is segment-local.
2. The band segments are **centred on the cuts**. `best/AKS/Bitonic/BlockSort.lean`'s aligned
   `blockSortNetwork` is the special case of segments at multiples of `2^b`. The Lean wiring needs the
   offset form (sort `[i − W, i + W)` in every column), which is the same proof with a shifted block
   index.
3. The cut layout requires consecutive cuts `≥ 2W` rows apart. That holds for the B blocks
   (`≈ m/k ≫ 2W`). The F₁|B₁ cut sits about `(π/2)/n ≈ 2.4e-4·m ≈ 4000` rows from the bottom, so its
   segment is clipped at row 0, which the proofs allow.

∎ (L3, full)

---

## L4, full proof (per-child form, REVIEW-v6 item 5)

**Notation.** For a node u, `Anc(u)` is the set of keys of range(u) located strictly above u.
* `Anc_L(u)` is the part that went up through an F₁ block whose sender held range(u) at its **low**
  extreme, i.e. the sender's low prefix contains range(u)'s lowest child;
* `Anc_H(u)` is the mirror part.

For a set S of keys of range(u), a **hole** of S is a key `x ∈ range(u) \ S` with x located at u or above
and `x < max S`, together with a witness `y ∈ S`, `y > x`. A crossing at an F-cut is a key placed on the
wrong side of the F₁|B₁ (or B_k|F₂) position cut, relative to the exact sort of that sender's bag.

**Claim L4.** At every time:
1. **(Segment.)** `Anc_L(u)` is a lowest segment of range(u), apart from at most `H_L(u)` holes, where
   `H_L(u)` is the number of F-cut crossings, in the most recent send of u and of each ancestor holding
   range(u) at its low extreme, that involve keys of range(u). Mirror for H.
2. **(Per child.)** For each child `w_h` of u, `|Anc_L(u) ∩ range(w_h)|` equals the spill-rule allocation
   of `|Anc_L(u)|`: fill the children from the low end, each capped at its actual deficit
   `G(w_h) = |range(w_h) \ subtree(w_h)|`, up to ± (the holes in range(w_h) and their witnesses).
3. **(Top.)** Nodes at level α(t) have `Anc = ∅`. This is the mirror of invariant E (§S2e): levels
   `< α(s)` are empty at the start of step s, because topDesc sends its whole bag down and topRise
   sends up only into level `α(s+1) = α(s) − 1`.

**Proof of 1** (induction on time). A key of range(u) is above u only if it was sent up in an F block by u
or by an ancestor whose bag contained it. Consider each way the set `Anc_L(u)` can change.
* **u sends.** F₁ receives the low outsiders and then the lowest keys of u's bag. By the induction
  hypothesis, `Anc_L(u)`'s keys are not in u's bag. Every key of range(u) below `max Anc_L(u)` that is not
  a hole is above u, so not in the bag either. Hence the keys of range(u) entering F₁ are the lowest
  remaining ones, and `Anc_L(u)` grows **contiguously** at its top. An F₁|B₁ crossing exchanges one
  should-go-up key with a should-stay key, creating at most one hole and one witness. Old holes inside u's
  bag (x at u) are now the lowest keys and go up first: **this send repairs them**.
* **An ancestor v holding range(u) at its low extreme sends.** By induction for v, `Anc_L(v) ∩ range(u)`
  is a lowest segment of range(u) (range(u) is at v's low extreme). v's F₁ takes v's lowest keys, the next
  ones above `Anc_L(v)`, so the union stays a lowest segment, with one hole per crossing.
* **The parent p sends u's block.** Keys of range(u) at p that are not in p's F₁ go down to u. They are the
  higher ones (exact sort), so `Anc_L(u)` **shrinks from its top** and stays a segment. Holes inside p's
  F₁ are repaired as above.
* **No other event** moves keys of range(u) above u: keys move only up through F blocks, or down from a
  parent to a child.
* **Interior range(u) at an ancestor.** If range(u) is not at v's low extreme, then v's F₁ contains keys
  of range(u) only when v's low prefix reaches u's range (a spill at v). Then all lower ranges of v are
  exhausted, and the same argument applies with v's "low extreme" read as "lowest non-exhausted range".

Holes persist only until the next send of the node holding them, so at any time they number at most the
crossings of the most recent sends along the chain. ∎

**Proof of 2.**
* Take the lowest segment of range(u), excluding keys inside the children's subtrees (which cannot be
  above u). It fills range(w₁)'s outside-subtree keys first: there are `G(w₁)` of them. Then it fills
  `w₂`'s, and so on. That is the spill rule with caps `G(w_h)`.
* Each hole removes one key from its child's count, and its witness adds one to (possibly) another
  child's count. Hence ±1 per hole or witness. ∎

**How the errors are charged.** The holes and witnesses at u's own F₁|B₁ cut are exactly the crossings
counted by `cB` (keys of range(w₁) and above that went into B₁ instead of F₁, and vice versa). That is
L3's `T(dB)` or Property B. Holes from an ancestor's F-cut are crossings at that ancestor's cut. For u,
they appear among the parent's intruders and deficits, which the width recursion carries in the inherited
half-width h (`N_L = O_L − D₁`; the parent's crossings at u's cut are in u's `N_L` interval, INDUCTION.md
§14). So L4's error terms coincide with crossings already in the type rules. **No new charge is
needed.**

**Design versus actual deficit.** The spill rule in the design uses the design deficits. The per-child
statement uses the actual `G(w_h)`, which differs from the design by the misdeliveries D (§2 of v6). The
allocation is 1-Lipschitz in the caps, so this difference is bounded by `Σ|D_h|` over the prefix children,
the same terms as in the shift identity. Hence `Σ_{h∈Pre_L} D_h^{anc} = G_L(u) + O(crossings)`, which is
the count form v6 §2 states. ∎

**Meeting prefixes.** When `θ_low + θ_high` exhausts every child's cap, all children are prefix children.
`width_sim.py` records `spill_children_max = 11 < k = 16` (low 9 + high 7 never meet). The code should
assert this rather than rely on it; the assert is added below.

**Lean status of L3a (2026-10-23).** The deterministic part is kernel-checked, with standard axioms only:
* `Chvatal.mergeBandPack2Net_low_crossings_le` (`best/AKS/Sub800/MergeBandPack.lean`): on a
  column-run-sorted 0–1 input, the low-set keys (`false`s) at rows ≥ i of the merge-first, band-repaired
  separator's output number at most `Σ_j (F_j − h)`. Here `F_j` is the low-set count in column j after the
  second sort, provided every band segment reaching rows ≥ i starts at row ≥ h.
* Components:
  * `Bitonic.segmentSort_cnt_rows_le` (one column);
  * `Chvatal.bandStage_rowCount_le` (through the scramble);
  * `Bitonic.cntT_rows_false_of_monotone` (the row identity);
  * `rowCount_comp_perm`, `rowCount_eq_sum_columns`.

Not in Lean: the probabilistic bound `Σ_j (F_j − h) ≤ T(margin)·mn`. That is the round-1 walk bound at a
margin, certified in interval arithmetic (`cert_walk_n.py tail`). L3b (band escapes at the cut, which uses
BULK2 round 2) is not in Lean either.
