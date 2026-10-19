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

The package's `F2R1Fail`/`F2R2Fail`/`F2R2Num` use closed forms that fail at these points. Lean
needs:
- the per-E sums (ψ* by bisection gives a rational witness);
- the tight R2 tail of FRINGE-CERT §3: the concave h and the certified H*;
- interval-free rational bounds on exp and log, as `F2R2Num` already does.

The certificates give every rational witness. Size: 1.5–3k lines, mostly numerics.

## W4. Bulk: the walk bound (ROUND2), the main new mathematics

Target: the fraction of σ that fail is at most 1/100 for round 1
(`HasCombinatorialPropertyBOnPipeline σ E1`) and at most 1/1000 for round 2
(`HasCombinatorialPropertyB2 σ E1 d`). These are exactly the predicates `Bulk2Exists` consumes.
Pieces:

1. **Deterministic duality** (ROUND2 §2): Σ_j X_j(δ_j) ≤ λR′ + Σ_j Y_j(λ), plus the base-row grid.
   Finite and combinatorial.
2. **Ville** for one column: P(Y⁺ ≥ x) ≤ e^{−θx} for θ ≤ θ*, as a finite-horizon exponential
   supermartingale over independent Bernoulli rows. It is a counting statement over the row
   permutations.
3. **Negative association** for one row's uniform s-subset indicator, then closure under
   independent rows and monotone functions of disjoint columns:
   E Π_j f_j ≤ Π_j E f_j.
   - The elementary route conditions on the overlap count, uses stochastic monotonicity (a
     coupling that adds one element), applies Chebyshev's sum inequality, and inducts over columns
     and then over rows.
   - This is the largest piece and is not in Mathlib.
4. **Round 1** (Freedman tail of the walk maximum, then the MGF by integration) is Lean-unfriendly.
   - Preferred: rederive round 1 by the same Ville/NA route as round 2, which avoids Freedman and
     integrals.
   - Before formalizing, check numerically that the substitute E1 still certifies the window.
5. **Numerics:** rational witnesses from `cert_walk.py`, with θ lower enclosures and Chernoff
   parameters per p-cell. There are many p-cells (about 220), so a uniform-in-p analytic argument
   or a Lean-side interval evaluator may be cheaper than one lemma per cell.

Size: 4–8k lines. This is the critical path.

## Order

1. Start W4 (pieces 3, then 2, then 1); it carries the most mathematical risk.
2. In parallel, run the round-1 substitute numerics (W4.4).
3. Do W2 next (mostly porting).
4. W3 and W1 are mechanical but long.

The headline would be `limsup D(n)/log₂ n ≤ 789.75`, assembled like `Chvatal1830Final`.
