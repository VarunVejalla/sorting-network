# Joint layers across a hierarchy of cuts

## Status

Investigation completed for exact layer accounting and finite diagnostics.
The proved base-two coefficient remains `3.270559...`; no improved coefficient
is claimed. The simplest joint-hierarchy and rank-update-saving arguments
have structural obstructions. The useful remaining target is a cumulative
orientation deficit constrained by interactions between successive layers.

## Joint partition ledger

For a layer, let `Y,Z` be its input/output, `R,S` the old/new partition
rank-set vectors, and `g=H(Y)-H(Z)`. Define

```text
V = H(S|R),
W = I(R;Z|S),
C = H(Y|R,Z).
g + H(S)-H(R) = V-W+C.
```

Here `R` is an input function and `S` an output function. Conditional on
`R,Z`, each crossing comparator's input orientation is determined by rank
membership. Only internal comparator orientations can remain ambiguous.
Thus, by the ordinary finite conditional-entropy support bound,

```text
0 <= C <= number of internal comparators.
```

Pure crossing layers have `C=0`, including layers with many crossing gates.
This reconstruction and capacity argument is derived, not formalized for an
actual Lean layer. `HierarchyRefinement.partition_layer_ledger` checks the
algebraic identity with its entropy quantities explicit. It does not prove
their interpretation, nonnegativity, or the comparator slot bound.

For complete rank-set history `T` and extension `T'=(T,S)`, define
`M=I(T;Y)`, `M'=I(T';Z)`. Joint history-bank accounting gives

```text
g + M'-M = H(S|T) + H(Y|T,Z).
```

`layer_history_bank_ledger` checks the expanded algebra. The new rank set
being an output function identifies the second term; this identification
still needs a layer-specific proof. The pure-crossing specialization
retains joint-entropy preservation as an explicit hypothesis.

## Joint histories collapse to the finest partition

Suppose each partition refines its parent. Coarse rank sets are unions of
fine rank sets; synchronously recorded coarse histories are functions of
fine histories. Therefore collecting them jointly adds no entropy:

```text
H(T_fine,T_coarse)=H(T_fine).
```

`entropy_refinement_joint`, `observationHistory_coarsen`, and
`entropy_joint_hierarchy_history` prove this generic deterministic statement
in Lean. At singleton leaves, the current partition is the whole rank vector.
Consequently a raw joint observation of every scale is not an extra source
of lower-bound information. This does not rule out conditional or weighted
quantities at separate levels.

Endpoint costs also matter. Initially a partition with block sizes `s_b` has
entropy `log_2(n!)-sum_b log_2(s_b!)`. Successive balanced refinement increments
are of order `n` per level. Summing increments to singleton leaves gives
exactly `log_2(n!)`, a leading-order cost. Equal-weight increments cannot be
hidden in an `O(n)` reserve. The script records endpoint budgets at n=8,32,128.

## Rank-update dependence is not comparison loss

Let `U_e` be the partition rank vector obtained by applying just gate `e`
to the layer input. For crossing gates, set

```text
S_rank = sum_e H(U_e|R) - H(S|R).
```

Given `R`, the tuple `(U_e)_e` determines the actual simultaneous update.
Its reduction to a final partition may hide which gate moved which ranks.
Thus

```text
S_rank = [sum_e H(U_e|R)-H((U_e)_e|R)]
           + H((U_e)_e|R,S).
```

The first bracket is conditional total correlation of rank updates; the
second is hidden gate-assignment entropy. Neither directly measures lost
comparison capacity.

For a scalable obstruction take uniform permutations on `n=2k` wires,
blocks `{0,...,k-1}` and `{k,...,2k-1}`, and the layer `(i,k+i)` for every
`i<k`. Each output has exactly `2^k` equally weighted predecessor permutations,
so the layer gains exactly `k` bits. Its output-conditioned orientation bits
are independent uniform bits: orientation total correlation is zero.

For each individual crossing gate, the preceding first-layer calculation
gives `H(U_e|R)>=log_2(k)`. Meanwhile the joint final rank set has at most
`binom(2k,k)` possibilities. Hence

```text
S_rank >= k*log_2(k)-log_2(binom(2k,k)) >= k*log_2(k)-2k.
```

This is `Theta(n log n)` rank-update saving in one fully efficient layer.
It disproves a direct charge of `S_rank` to comparison loss, even with an
`O(n)` allowance. It does not refute a general history potential or a lower
bound above 4. This combinatorial/entropy argument is derived, not kernel
checked. The JSON includes its analytic lower bounds at n=16,...,256.

## Hierarchy levels reorganize actual orientation entropy

Assign each gate to the first hierarchy split separating its endpoints.
Let `O_j` be that group's orientation bits, `q_j` its gate count, and `R_j`
the input partition at level `j`. Put `C_0=g`, and
`C_j=H(Y|Z,R_j)` after successive refinements. At singleton leaves `C=0`.

Given `Z`, old partition rank sets identify precisely the orientations of
gates crossing that partition. Conversely those orientations reconstruct
the old rank sets from `Z`: internal gates preserve block membership.
Consequently

```text
A_j = C_j-C_(j+1) = H(O_j | Z,O_0,...,O_(j-1)),
0 <= A_j <= q_j,
g = sum_j A_j,
comparison loss = sum_j (q_j-A_j).
```

The structural entropy interpretation and inequalities are derived, not
kernel checked. `hierarchy_gain_telescope` and `hierarchy_deficit_identity`
prove the abstract accounting, keeping the terminal-loss condition explicit.
This is a chain-rule organization of orientation entropy; it supplies no
strict deficit by itself. Uniform first-layer examples attain all level
capacities simultaneously.

## Exhaustive five-wire results

The probe uses all 7101 reachable distributions and all 25 nonempty disjoint
layers: 177525 instances, for coarse blocks `{0,1}|{2,3,4}` and finer blocks
`{0}|{1}|{2}|{3,4}`, followed by singleton leaves. Prefix multiplicities and
full-slot certificates are exact integers; entropies are numerical.

- Layer-ledger discrepancy: at most `1.8e-15`.
- Pure-crossing conditional loss: exactly zero numerically.
- Hierarchy/group orientation identity discrepancy: zero numerically.
- Level slot bounds exceedances: at most `8.9e-16` (roundoff).
- Maximum rank-update saving: `2.342446` bits, but orientation dependence
  in that witness is only `0.004026` bits.
- At a certified two-bit-gain layer, rank-update saving is `1.655819` bits;
  orientation dependence is zero. This is the initial layer `(0,2),(1,3)`.
- A genuine orientation-dependence witness has prefix `(1,3),(2,4)` and
  layer `(1,2),(3,4)`: gain `5/3` numerically and deficit `1/3`, wholly
  accounted for by orientation dependence.

These are finite diagnostics, not asymptotic bounds.

## What to investigate next

The target must concern **successive layers**, not a strict inequality for
every isolated layer. Use the unique first-separating split to count each
gate once, then seek a constraint on conditional orientation bias and
dependence that persists when information moves between levels.

1. Formalize the layer reconstruction and group-orientation interpretation.
2. Track each level's orientation information across a bounded time window.
3. Find a structural rule forcing either lost orientation capacity or progress
   in a bank with subleading endpoints. Check it against the independent
   matching obstruction before attempting a full asymptotic proof.
4. Relate it to the established Kahale certificate bound; an improvement must
   exploit sorting constraints absent from the saturating Fibonacci relaxation.

For coefficient above 4, the amortized deficit must exceed half of all
comparison slots, up to subleading errors. Nothing here proves that rate.

## Reproduction

```text
lake build AKS.Kahale.HierarchyRefinement AKS.Kahale.HierarchyRefinementAxioms
python -B scripts/kahale_hierarchy_layer.py --wires 5 --output docs/kahale-hierarchy-layer-results.json
```

See [results](kahale-hierarchy-layer-results.json) and
[the preceding rank-set transition investigation](kahale-rankset-transition.md).
