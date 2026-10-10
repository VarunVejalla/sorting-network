# Ideas examined and ruled out (with reasons)

Keep this list so nobody repeats them.

* **Sharper Lemma 6.1 via McDiarmid / bounded differences (claimed ~20× on ε_B).** Wrong. Moving one
  row's permutation changes up to ~n column sums (Lipschitz Θ(n)), so the exponent loses the
  factor `n`. The `ln m` in `ε_B ≥ √(2(1+ln m)/m)` is the entropy of the *input* union
  (`(m+1)^n` column-sum vectors) against a fixed σ, not a Hoeffding artifact. Best achievable
  with a net on the column sums: constant ≈ 6.5–7 instead of 9.07 (~1–2% of the slope).
  Chebyshev/second-moment routes cannot give failure `e^{-Θ(n ln m)}`.
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
* **Run-aware first sort beyond uniform s = 29.** Stage-dependent block size gives only ~1.5%
  more; an ideal merge tree of the actual (non-power-of-two) runs caps at about −16% in total
  (first sort ≈ 1209 instead of 1770).
