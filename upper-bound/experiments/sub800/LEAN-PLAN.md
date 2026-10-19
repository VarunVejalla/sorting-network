# Lean plan for the R1 sub-800 bound

Planning note, 2026-10-19. Nothing here has been built.

The proof (R1-PROOF.md) splits into four Lean workstreams. Each has its own interface to the 1419
package (`../../best`), so they can proceed in parallel.

## W1. Tree with a per-node flow table (design P)

Replace the uniform `FlowTable`/`FlowSizes7`/`NodeShape` by the deficit recursion of R1-PROOF §1.
Then prove (I1)–(I4) by induction over the schedule, and generalize Lemma 4.1/4.2 to per-child
blocks (Lemma 4.1′/4.2′).

- **Starting point.** UB-12's `experiments/slackfree-lean` (branch `worktree-runaware`): Stage 1a
  and 1b-1 are done. `FlowTableB`, `FlowFacts`, and `wireSets`/`execPlacement`/`stagesNet` are
  already generic over the table. Stage 1b-2 (per-child windows, deficit-form Lemma 4.1, per-child
  `bad_send0_real`) is the next step, as INTERFACE.md §4 describes.
- **New relative to UB-12.**
  - The parameters (16, 32, 1/8): new `Schedule` numerals, t_f = 3d − 14, and the bottom-ratio
    table by t mod 6.
  - Design P instead of D2: θ_end = π/2 + G − r*c and interior shares of 2s − G.
  - The invariant G ≤ g*·c, an inequality over the per-node state, not a closed form.
  - a ≤ (1 + 7/4096)·c.
- **Size.** UB-12 estimated 2.5–4k lines for this route (R1).

## W2. Separator: padded two-round module at the new geometry

`paddedPack2Net` with `paddedPack2Net_all_cut_bounds` and `_fHigh/_fLow_baseline` already exist,
kernel-checked, in `experiments/tapered`. W2 has to:
- port them into the package;
- instantiate the geometry rule of R1-PROOF §4 (fringe classes 7934 and 406109; the topDesc
  bulk-only rectangle; m+1 ≤ 2^26; n = ⌊π/(2(f+1))⌋) together with the support inequality;
- show depth 3·S(26) via `SeparatorDepth`;
- use Batcher's sort for a ≤ 2^45 (`AKS/Bitonic`).

Size: about 1k lines.

## W3. Fringe witnesses at δ_F = 1/8, J = 190,000 (per-E route)

First add a δ field to `F2Params`: `jmax` and the Chernoff preconditions hard-code 128/4095.

The package's `F2R1Fail`/`F2R2Fail`/`F2R2Num` use closed forms that fail at these points. Lean
needs:
- the per-E sums (ψ* by bisection gives a rational witness);
- the tight R2 tail of FRINGE-CERT §3: the concave h and the certified H*;
- interval-free rational bounds on exp and log, as `F2R2Num` already does.

The certificates give every rational witness. Size: 1.5–3k lines, mostly numerics.

## W4. Bulk: the walk bound (ROUND2), the main new mathematics

**Status (2026-10-19): formalized in `lean/`, standard axioms only, with the numerics left as
explicit hypotheses.** Build with `bash lean/build.sh`.

| module | content |
|---|---|
| `NegAssoc` | negative association of a uniform k-subset; independent rows; product over disjoint column sets |
| `Ville` | Ville's inequality for walks with independent rows (counting form) |
| `LayerCake` | discrete layer cake: exponential moment from a geometric tail |
| `RowMgf` | one column bit under a uniform k-subset |
| `Pushforward` | uniform scramble → independent uniform row subsets |
| `Round2Det` | reduction of `onesAboveBottom` to column walks; weak duality; displacement ≤ 2·excess + n·|i−b| |
| `Round2Col` | split of the dual variable into forward/backward Ville walks; Ville tails; column moment |
| `Round2Fixed` | fixed (S, b): `#{x ≤ Σ_j Y_j} ≤ e^{-tx} M^n #Scramble` |
| `Round2Union` | `round2_fail`: failures of the package's `HasCombinatorialPropertyB2` |
| `Round1` | `round1_fail`: failures of `HasCombinatorialPropertyBOnPipeline`, by the same route (no Freedman) |

The Lean route uses two weaker but formalization-friendly steps:
- e^{t max(a,b)} ≤ e^{ta} + e^{tb} − 1, which needs no independence of the two walks;
- round 1 by Ville with drift instead of Freedman.

Numerically this gives d = 8.74e-6 against ε_B = 9.52e-6 at 2^25.6 (float).

**Remaining (W4.5): numerics.** For every n ≥ 16 and every row count in [2^25.6, 2^26], each size
s needs parameters satisfying the hypotheses of `round1_fail` and `round2_fail`, with failure
sums ≤ 1/100 and 1/1000.
- Per-column reduction: choose x_s to make each union term η/(n−1). Use
  ln C(n,s) ≤ n·H(s/n) and the decrease of ln((n−1)/η)/n.
- With fixed parameters the conditions are monotone in m, so one check at m = ⌈2^25.6⌉ per p-cell
  covers the window.
- This needs a certified exp/log bound library (Taylor with remainder plus rational evaluation by
  `norm_num`), shared with W3, and generated per-cell lemmas (round 2 is symmetric in p ↔ 1−p).

## Order

1. Start W4 (pieces 3, then 2, then 1); it carries the most mathematical risk.
2. In parallel, run the round-1 substitute numerics (W4.4).
3. Do W2 next (mostly porting).
4. W3 and W1 are mechanical but long.

The headline would be `limsup D(n)/log₂ n ≤ 789.75`, assembled like `Chvatal1830Final`.
