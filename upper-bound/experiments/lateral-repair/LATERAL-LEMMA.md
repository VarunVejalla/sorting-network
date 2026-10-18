# Worst-case bound for the lateral residual

UB-20 · 2026-10-18 · Claude (Opus 5.5).

**Claim level: hand-proof, unaudited**, resting on one cited concentration inequality (Lemma 2),
whose exact constant should be checked against the source. Lemma 1 is exact and is also checked
numerically (`check_staircase_lemma.py`, `check_staircase_lemma.out`). No sorting bound follows
from this note alone.

## Setting

Siblings `v_j` and `v_{j+1}` (children of the same node `u`) each hold an `m x n` matrix and run
the two-round separator of the 1419 package:

```text
sort columns, scramble rows (sigma1), sort columns, scramble rows (sigma2), sort columns.
```

A row scramble applies an independent permutation of the `n` columns to each row. At the previous
stage, `u`'s separator spilled keys across the cut `t_j` between the siblings' ranges: `P` keys
above `t_j` landed in `v_j` and `Q` keys below `t_j` landed in `v_{j+1}`. When `u`'s block size
equals its key count, `P = Q` exactly. Otherwise `|P - Q|` is the net cut drift (slack and
outsider shifts), which the Chvatal budget (4.2) charges separately and lateral repair does not
touch.

**Lateral step.** After both siblings' separators and before routing, for every column `c`, merge
column `c` of `v_j` with column `c` of `v_{j+1}`. Both are sorted, so with one fixed reversal this
is a bitonic merge of depth `lg(2m)`. The `m` smallest keys go to `v_j`'s column `c` and the `m`
largest to `v_{j+1}`'s. Both columns stay sorted, so every row-position meaning (fringe rows,
child blocks) is preserved. Each bag borders siblings on both sides, so a stage runs the step in
two phases (even boundaries, then odd), costing `2 lg(2m)` layers.

## Lemma 1 (staircase representation; exact)

Fix a threshold, and let `S` be the keys of a sorted-column matrix above it, with `cnt[c]` of them
at the top of column `c`. After a row scramble with independent uniform permutations and a column
sort, column `T` holds

```text
p_T = sum_i X_{i,T},   X_{i,.} = indicator of a uniformly random a_i-subset of the columns,
a_i = #{ c : cnt[c] > i },
```

independently over rows `i`. So the law of `p` depends on `cnt` only through the nonincreasing
**profile** `(a_0, ..., a_{m-1})`, `sum_i a_i = |S|`.

*Proof.* Row `i` contains a key of `S` exactly in the columns with `cnt[c] > i`; its permutation
sends that `a_i`-set to a uniformly random `a_i`-set, independently of other rows. A column sort
only counts. ∎

Consequences, writing `lam = P/n`:

* `E p_T = lam` and `Var p_T = sum_i (a_i/n)(1 - a_i/n) <= lam`, so `E sum_T |p_T - lam| <= n sqrt(lam)`.
* The number of possible profiles is at most `binom(m+n, m)` (monotone lattice paths), however
  the adversary chose the input.

## Lemma 2 (cited concentration for random subsets)

If `A` is a uniformly random `k`-subset of `[n]` and `g` changes by at most `c` when one element of
`A` is swapped for one outside it, then `P(g - E g >= t) <= exp(-2 t^2 / (min(k, n-k) c^2))`.
This is McDiarmid's bounded-differences inequality for sampling without replacement (exposing the
`k` chosen elements one at a time; the `n-k` case by complementation). Over independent rows the
variance proxies add.

Here `f = sum_T |p_T - lam|` changes by at most `c = 2` under one swap in one row. So for a fixed
profile,

```text
P( f > n sqrt(lam) + t ) <= exp( -t^2 / (2 S) ),   S = sum_i min(a_i, n - a_i) <= P.
```

## Theorem (residual for every input)

Choose `sigma2` independently and uniformly at random for each sibling shape. With probability at
least `1 - 1/(2mn)`, for **every** input, every spill size `P`, and both orientations (top extreme
set in `v_j`, bottom extreme set in `v_{j+1}`),

```text
sum_c |p_c - lam| <= n sqrt(lam) + sqrt( 2 P ( ln binom(m+n, m) + ln(4 m n) ) ).
```

*Proof.* Union bound over the at most `mn` values of `P`, both orientations, and at most
`binom(m+n,m)` profiles, using Lemmas 1–2 with `t^2 = 2P(ln binom(m+n,m) + ln(4mn))`. ∎

The same random choice must also satisfy the separator's existing Properties B and F. Their
failure budgets are separate events, so existence of a common `sigma2` needs only the total failure
probability below one.

**Residual after the lateral step.** In the symmetric case `P = Q` (common mean `lam`), the merge
cancels `min(p_c, q_c)` misplaced pairs in column `c`. The residual is

```text
sum_c |p_c - q_c| <= sum_c |p_c - lam| + sum_c |q_c - lam|.
```

Dividing by `P = n lam`, with `ln binom(m+n,m) <= min(m,n) ln(e (m+n)/min(m,n))`,

```text
rho <= 2 ( 1 + sqrt( 2 [ln binom(m+n,m) + ln(4mn)] / n ) ) / sqrt(lam).
```

For `n >= m` the bracket over `n` is at most `ln(2e) + o(1)`, giving `rho <= 5.7/sqrt(lam)`.
For `n = m/16` it gives `rho <= 7.5/sqrt(lam)`. In the model's form `rho = 2 sqrt(C/(pi lam))`
these are **C ≈ 26 and C ≈ 44** (`lateral_worstcase_rows.py`). Bags with very few columns are
worse, but their absolute spill is small; they need a separate small-bag treatment, for example
exact sorting (UB-22).

The structured adversaries in `sim_lateral_residual.out` reached only `C <= 0.5`. The theorem's
constant is a factor of 50–90 more pessimistic: it ignores the sub-Poisson variance
`sum_i (a_i/n)(1-a_i/n)` (5.3 against `lam = 16.7` in the check) and pays the full profile union.

## Lemma 3 (the step never hurts the boundary it repairs)

For the cut `t_j` and any column pair, let `p` be the keys of `v_j`'s column above `t_j` and `q`
the keys of `v_{j+1}`'s column below `t_j`. After the merge, `v_j`'s column has `(p - q)_+` keys
above `t_j` and `v_{j+1}`'s has `(q - p)_+` below it. So wrong-side counts across this boundary
never increase, for this threshold and, by monotonicity of comparators, for every threshold.

*Caveat.* A key below `t_{j-1}` that sat in `v_{j+1}` can move into `v_j`. It moves closer to its
correct node, but it raises `v_j`'s count of keys belonging to `v_{j-1}`. Under locality such
far keys are second order (`eps_2 = O(eps_B^2)` in mass, `../tapered/NOTES.md` §2.2). The
per-node form of the Chvatal invariant still has to absorb this shift; see open items.

## What remains open

1. **Composition with the invariant.** Lemma 3 gives monotonicity at the repaired boundary. The
   per-node outsider counts must still be shown to stay within `mu delta^r c` after the shift of
   far keys between siblings and after the second phase acts on the first phase's output.
2. **Unequal siblings.** End children under a non-uniform flow table (UB-12) have different sizes;
   pair `min(n_j, n_{j+1})` columns and charge the unpaired spill.
3. **Constant audit.** Check Lemma 2's exact constant in the source, and whether the union over
   profiles can be shared with the existing Property B/F union.
4. **Small fringe floor (UB-15).** The model shows lateral repair only pays off once the fringe
   floor drops below about 1024 rows.
