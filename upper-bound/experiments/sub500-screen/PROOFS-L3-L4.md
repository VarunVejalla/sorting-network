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
