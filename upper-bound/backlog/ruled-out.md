# Ideas examined and ruled out (with reasons)

Keep this list so nobody repeats them.

* **Sharper Lemma 6.1 via McDiarmid / bounded differences (claimed ~20× on ε_B).** Wrong. Moving one
  row's permutation changes up to ~n column sums (Lipschitz Θ(n)), so the exponent loses the
  factor `n`. The `ln m` in `ε_B ≥ √(2(1+ln m)/m)` is the entropy of the *input* union
  (`(m+1)^n` column-sum vectors) against a fixed σ, not a Hoeffding artifact. Best achievable
  with a net on the column sums: constant ≈ 6.5–7 instead of 9.07 (~1–2% of the slope).
  Chebyshev/second-moment routes cannot give failure `e^{-Θ(n ln m)}`.
  **Update 2026-10-18 (UB-29):** the `ln m` is inherent only to arguments that take a union over
  input states. `experiments/walk-bound/WALK-BOUND.md` removes it by decomposing the centered
  excess into per-column random walks: the adversary's choice of heights becomes one walk maximum
  per column, and only a union over output sets `S` (cost `ln 2` per column) remains. Round 1 is a
  reviewed hand proof (`E1 ≈ 2.35/sqrt(m)` at `n = 16`, against `sqrt(2(1+ln m)/m)`); round 2 is a
  sketch. The McDiarmid route above is still wrong as stated.
* **Expander ε-halvers as the separator.** Depth ∝ 1/ε (≈ 2^26 for ε = 2^-26); sort-based
  separators win for ε < 2^-4.
* **Zone-shrinking later rounds** (multi-round where round `t` only sorts rows near the 66
  boundaries, heights `m^{1/2}, m^{1/4}, …`). The first round controls only the L1 mass of
  the excess, not per-column tails; an adversary choosing the input after σ can put deviation
  ≈ √(m·n) into one column, so zones need height ≳ √(m n), which is useless for top-level nodes
  (n > m) that set the stage depth.
* **Full-height extra rounds.** `(scrambles, lg m, coefficient)` = (2, 42, 1354), (3, 38, 1482),
  (4, 36, 1665) (`docs/chvatal-two-round-separator.md`): more full sorts cost more than the
  smaller `m` saves.
* **Columnsort-style deterministic dirty-region bound** (Leighton). Displacement ≤ (s−1)² positions
  gives ε ≈ s/r, which grows with the number of columns `s = n`; useless for top-level nodes.
* **Designed (low-discrepancy / Latin / affine) round-1 scrambles to lighten the 1/W tail**
  (2026-11-07, `experiments/chvatal/DESIGNED-SCRAMBLE.md`). For n ≥ m with distinct destinations
  per column, a random target set gives every design the same tail, ≳ 0.16/W (hand bound, which
  matches the attack within about 5%). Structured shift designs are 30–300× worse. Latin blocks help
  only for m > n (small nodes).
* **Run-aware first sort beyond uniform s = 29.** Stage-dependent block size gives only ~1.5%
  more; an ideal merge tree of the actual (non-power-of-two) runs caps at about −16% in total
  (first sort ≈ 1209 instead of 1770).
* **One-round separator with walk-bound precision (2 sorts per stage), UB-37 screen 2026-10-20.** E1(m)
  of the walk bound is too weak: the best schedule needs rows of `2^32` and prices to 880, above 789.75.
  Two sorts only help if the two-round precision is kept (UB-32).
* **Larger δ_F at the R1 schedule (4,5,3).** (4.3) caps μ at `ν/(Ak²)`, about the (4.4) value at
  `δ_F = 1/8`. With the certified fringe fits, `δ_F = 1/5` prices to 800 and the extrapolated 1/4 or 1/3
  to 850 (`experiments/sub500-screen/SCREEN.md`).
* **More ε_B tolerance alone.** At the R1 point the fringe floor binds: tolerance ×10 to ×1000 leaves
  789.8. It must come with a fringe improvement (UB-34/UB-40).
* **Warm-start separators (UB-47, inherited column balance; sort + scramble + band per stage)**
  (2026-11-11, `experiments/warm-start/WARM-START.md`). The real layout stacks F ~ A/nu fringe fragments
  per column. The per-stage worst case is attained by sets aligned with the next stage's groups (Lemma G
  is tight), giving an F^2 leak and 335 (R1) at attack constants. A stage-0 input can steer two stages
  ahead (correlation 0.99), so reachability gains at most about 2x (295 R1 even then). A whole-run (amortized) attack
  shows the reachable leak falls about 5x per stage after the free input, but with zero leak R1 still
  floors at 283.9 at attack constants (band/fringe terms), so amortization cannot rescue it either.
