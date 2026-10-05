# Two-block transitions and fresh versus recycled information

## Status

The proved base-two lower-bound coefficient remains `3.270559...`.
New Lean modules prove crossing reconstruction, a signed rank-set transition
identity, the sum of two boundary-transfer identities, and a budget for fresh
innovation. Conditional data processing and a larger coefficient remain open.

## Exact crossing update

Let `Y` be the previous rank vector, `Z` its comparator output, `R` the old
rank set of one crossed block, and `S` its new rank set. `(R,Z)` reconstructs
`Y`: the unchanged block ranks are known from `Z`, so `R` identifies the old
endpoint rank; the sorted endpoint pair determines the other rank. Thus

```text
H(Y)=H(R,Z),    g=H(Y)-H(Z)=H(R|Z).
V=H(S|R),      W=I(R;Z|S),
g + H(S)-H(R) = V-W.
```

`RankSetTransition.crossing_reconstruction_fibers` proves reconstruction and
`crossing_reconstruction_entropy` proves the entropy equality, preserving
actual prefix multiplicities. The encoding uses natural-number ranks and
arbitrary unchanged data. The old endpoint rank must lie outside the
unchanged block rank set. A wrapper for projected `Comparator n` execution
has not yet been added.

`crossing_rankSet_ledger` proves the signed identity. `S` is determined by
`Z`, so the expanded residual expression is conditional mutual information.
Its nonnegativity is still unproved in Lean. `two_block_boundary_transfer`
adds the insertion/coupling updates for both touched blocks, with all four
distinctness conditions explicit.

## Static linear redundancy

For complementary blocks `A,B`, set

```text
L_A=H(Y_A)-H(R_A),  L_B=H(Y_B)-H(R_A),
K_A=H(Y_A)+H(Y_B)-H(R_A)-H(Y).
H(Y)=H(R_A)+L_A+L_B-K_A.
```

Complementarity makes the two rank sets equivalent observations.
`complementary_block_ledger` checks the algebraic relation. Coupling adds no
linear coordinate when rank-set entropy, both order entropies, and whole
entropy are already available. Averaging and endpoint centering preserve the
relation. This does not rule out nonlinear, joint, or history-based potentials.

## Innovation must retain its signed counterpart

The exhaustive five-wire probe covers all 7101 reachable distributions and
178848 nontrivial crossing/block instances. One example is

```text
prefix: (0,1), (0,2), (2,3), (2,4)
gate: (1,2), block: {0,2}
gain: 0.229574; innovation: 2.297323;
rank-set entropy rise: 2.067436; residual: 0.000313.
```

Maximum identity discrepancy is `1.4e-15`. No nontrivial exact-zero-gain
transition occurred in this catalogue; that is finite evidence only.
Counts are exact integers; entropies are numerical.

There is also a derived analytic obstruction. Start with uniform permutations,
a size-`k` block, and its first crossing comparator. Let `v=k(n-k)` and let
`m(r)` count pairs with the inside rank greater than the outside rank, given
old rank set `r`. Each endpoint pair is uniform among `v` choices. Each
inversion produces a distinct new set; other pairs leave the set unchanged.
Consequently

```text
H(S|R=r) = (m(r)/v)*log_2(v)
            - (1-m(r)/v)*log_2(1-m(r)/v).
```

Rank reversal gives `E[m(R)/v]=1/2`, hence

```text
(1/2)*log_2(v) <= V <= (1/2)*log_2(v)+1/(e*ln(2)).
```

For balanced even `n`, `V >= log_2(n)-1` per comparator. The gate gains
exactly one bit. The initially uniform rank set has maximal entropy, so
`H(S)-H(R)<=0`, and the ledger gives `W >= V-1 >= log_2(n)-2`.
Innovation and residual dependence both grow logarithmically even at the
first gate. Separately bounding them loses their essential cancellation.
This argument is derived, not kernel checked.

The script evaluates the formula and exact output rank-set counts at widths
4,6,8,12,16,20. At width 20: `V=3.795714`, `W=2.848142`, rank-set entropy
change `-0.052428`. The extra uncertainty describes rank membership changes;
the comparison still gains only one bit.

## Fresh innovation and a checked history budget

Let `T_t=(R_0,...,R_t)` be the complete rank-set history. Distinguish

```text
Markov innovation: H(R_(t+1)|R_t),
fresh innovation: H(R_(t+1)|T_t)=H(T_(t+1))-H(T_t).
```

For arbitrary observations determined by initial input `X`,
`HistoryInnovation` proves

```text
fresh_t >= 0,
sum fresh_t = H(T_d)-H(T_0) <= H(X)-H(T_0).
```

For uniform permutations and a size-`k` cut this budget is
`log_2(k! (n-k)!)`: leading order for balanced cuts, not an `O(n)` exception.
Only deterministic entropy monotonicity and telescoping are needed for these
checked results; conditional data processing is not assumed.

An exact-state dynamic program maximizes cumulative Markov innovation,
averaged over all size-two subsets, along five-wire sequential sorting paths.
An integer positional moment strictly increases on every changed state and
orders the transitions without numerical entropy comparisons. The maximum
is `5.254855` bits. On that same ten-comparator path, fresh innovation is only
`2.696824` bits; its general budget is `log_2(2!*3!)=3.584963` bits. This
demonstrates recycling and is not a depth-optimality calculation.

## The next structural inequality

Consider the history bank `M_t=I(T_t;Y_t)`. At a crossing gate the old history
determines `R_t`, so `(T_t,Y_t)` and `(T_t,Y_(t+1))` have identical fibers.
Adding the new rank set to history preserves joint entropy with the output.
Entropy expansion therefore gives

```text
crossing: g_t + delta M_t = fresh_t,
internal: g_t + delta M_t = H(Y_t|T_t)-H(Y_(t+1)|T_t).
```

`CrossingHistory.crossing_history_bank_update` now proves the first identity
for the natural-rank encoding, under an explicit decoder from history to the
old rank set. `fixed_history_bank_update` proves the second algebraic identity
for arbitrary input/output observations with fixed history. The actual internal
comparator projection and quantitative inequalities remain separate obligations.
Initially
`M_0=H(R_0)=O(n)` for a balanced cut; finally `M_d=0`. Endpoint cost is
acceptable. The unresolved obstacle is leading-order fresh innovation and
its interaction with conditional internal losses.

Next: specialize the identities to network layers and prove conditional information inequalities,
then investigate **joint parallel-layer updates across a hierarchy of cuts**.
We need a quantitative restriction on fresh history information and
conditional internal information that a layer can remove together. No such
restriction is proved, and the present results do not justify predicting
a coefficient above 4.

## Reproduction

```text
lake build AKS.Kahale.RankSetTransition AKS.Kahale.RankSetTransitionAxioms AKS.Kahale.HistoryInnovation AKS.Kahale.HistoryInnovationAxioms AKS.Kahale.CrossingHistory AKS.Kahale.CrossingHistoryAxioms
python -B scripts/kahale_rankset_transition.py --wires 5 --output docs/kahale-rankset-transition-results.json
```

See [the machine-readable probe](kahale-rankset-transition-results.json) and
[the preceding transfer investigation](kahale-transfer-charging.md).
