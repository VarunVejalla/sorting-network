# Modular whole-layer and relative-order banks

## Status and target

The proved lower-bound coefficient is still `3.270559...` for base-two logs.
The target is now **above 4**, if a structural inequality supports it. Nothing
in the current investigation proves an increased coefficient.

| Saving fraction `rho` | Leading coefficient `2/(1-rho)` |
|---|---:|
| 1/2 | 4 |
| 9/17 | 4.25 |
| 5/9 | 4.5 |
| 3/5 | 5 |

We keep `rho` a parameter rather than hard-code coefficient 4.

## Whole-layer information accounting

For a parallel layer with `m` gates, let `S` be its swap-bit vector and `W`
its entire rank output. The output and swap bits reconstruct the predecessor,
so the joint entropy loss is `h=H(S|W)`. Define

```text
bias deficit = sum_g [1-H(S_g|W)]
dependence deficit = sum_g H(S_g|W) - H(S|W).
```

Then `m-h` is their sum. Both deficits are nonnegative by the binary entropy
bound and conditional subadditivity. These entropy interpretations are derived
mathematical statements, not yet Lean entropy theorems. The Lean module only
proves the associated algebraic identity.

This decomposition uses whole-layer conditioning. It does not sum entropy
gains of isolated gates computed at the initial prefix. In the sorted-block
example each orientation bit is conditionally fair, and the entire saving is
dependence between bits.

## A simple snapshot bank fails

Let `Q(Y)` be the maximum dependence deficit among available matchings applied
to the current distribution. It is zero both for uniform input permutations
and for the final singleton rank state. Consider

```text
B = kappa*U - lambda*V - beta*Q,
```

where `U` counts uniform rank marginals and `V` counts fixed rank marginals.
For `n>=2`, the endpoints give `B_0-B_d=(kappa+lambda)*n`.

The [finite investigation](kahale-layer-bank-results.json) exhaustively covers
9, 119, and 7101 reachable rank distributions on 3, 4, and 5 wires. Different
prefixes with identical distributions may be merged: all future distribution
updates and these statistics depend only on that distribution. Integer fiber
weights are exact; entropy and linear programming are numerical.

On five wires, the best pointwise charge fraction for this linear bank is
about `0.959148` when `beta>=0`, and `0.956556` with either sign allowed.
These are finite numerical diagnostics, not universal coefficient bounds.
In particular, they do not refute a bank with a separate bounded exception
budget, nor a different nonlinear bank.

Two transitions with unchanged `U,V` explain the obstruction: one increases
`Q` and gains `1.893785` bits; another decreases `Q` and gains `1.918296` bits.
No sign of its coefficient simultaneously pays for both. Their weighted
combination cancels the `Q` change and forces charge fraction at least
`0.956556` within this family. The counts and witness prefixes are recorded.

There is also an unchanged-`U,V,Q` transition gaining `1.236453` bits, above
the one-bit layer budget required by `rho=1/2` on five wires. Equality of `Q`
here is observed numerically; no kernel-checked equality is claimed.

The four-wire block plus one separate wire illustrates why fixed global
rank is too narrow: completing the block fixes its relative order but does
not fix any of its absolute ranks.

## A centered relative-order bank

For a subset `A` of `k` wires, let `R_A` be its unordered rank set and `P_A`
the ordering of those ranks among its positions. This pair reconstructs its
rank vector, giving

```text
H(P_A | R_A) = H(Y_A) - H(R_A).
```

Initially this conditional entropy is `log_2(k!)`; at the sorted endpoint it
is zero. Define the normalized average over all subsets of size `k`:

```text
J_k = (n/k) * average_A [log_2(k!) - H(P_A | R_A)],
K_k = (n/k) * log_2(k!),
I   = log_2(n!) - H(Y),
R_k = J_k - [K_k/log_2(n!)] * I.
```

Thus **every `R_k` is zero initially and finally**. This is a normalized
subset average, not an assertion that the subsets form a disjoint partition.
The extremal sizes `k=1,n` give identically zero banks. Intermediate sizes
measure relative-order information that is invisible to absolute fixing.
Entropy reduction alone does not certify that a relative order is the correct
sorting order; the bank measures information.

A candidate is `B=sum_k w_k*R_k+kappa*U-lambda*V`, optionally including other
features. Its endpoint cost is still only `(kappa+lambda)*n`, even across many
scales. The weights may depend on `n`, but must be fixed along the execution
unless their changes are fully included in the local budget.

The [relative-order diagnostic](kahale-relative-order-bank-results.json) shows
that this bank distinguishes the offending transitions. On five wires,
`R_4` increases by approximately `0.130617` and `0.266774` on the opposing
`Q` transitions. This suggests a negative weight could pay for both there.
It does not show that the same weight works on other transitions.

The [full finite challenge](kahale-relative-order-challenge.json) examines
linear combinations of all intermediate scales on every five-wire transition,
with total boundary credit capped at `2n`. Fitting is a way to challenge this
specific functional form; a finite fit is not evidence of an asymptotic bound.
The best numerical charge fraction is approximately `0.823394`, well above
the `0.5` target. The optimum uses less than `n` of boundary credit, so the
chosen cap is not binding. Thus this simple linear bank is insufficient for
the proposed pointwise inequality, even though it distinguishes the earlier
witnesses. An additional controlled exception term could change that conclusion.

The output includes a numerical dual obstruction supported on just four
transitions. Their positive weights give total comparison capacity one,
average information gain `0.823394`, and zero drift in every intermediate
relative-order bank (to floating-point precision). Their uniform and fixed
wire counts are unchanged, and the multiplier for the boundary cap is zero.
Thus boundary-credit size is not what prevents this particular fit. These
are transitions from different prefixes, not one realizable network path;
they obstruct the proposed pointwise linear inequality rather than establish
an asymptotic barrier for all possible methods. The dual certificate still
needs rigorous error bounds or a kernel proof before it is a theorem.

This directs the next investigation toward dependence between relative-order
constraints, or a nonlinear bank retaining more than their scale averages.
It does not justify formalizing a large entropy library on the assumption
that a linear combination of these averages will suffice.

## Modular proof obligations

| Module | What is checked | What remains separate |
|---|---|---|
| `FiniteFibers` | composition and total-mass counting | entropy of weighted fibers |
| `ComparisonTrace` / `RankFiberMerge` | reconstruction and two-predecessor counts | conditional entropy interpretation |
| `AmortizedAccounting` | summing local budgets with explicit errors | proving those local budgets |
| `LayerBank` | endpoint algebra and coefficient conversion | rank-statistic endpoint interpretation |
| `RelativeOrderBank` | centering and weighted endpoint cancellation | subset entropy definitions and transitions |

All of these focused Lean modules and the guarded axiom audits build. Audited
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. In particular,
`amortized_information_budget` is conditional: the structural inequality is
an explicit hypothesis, not a newly proved sorting bound.

The next mathematical lemmas should be:

1. **Weighted conditional entropy:** formalize finite distribution chain rules
   from exact integer fiber weights; never replace them by uniform-image counts.
2. **Subset reconstruction:** prove the rank-set/relative-order factorization
   and its initial/final conditional entropies.
3. **Internal comparator:** if both endpoints lie in `A`, its rank set is
   preserved. Its relative-order entropy reduction is at least the full-state
   information gain, by conditioning on the projected output rather than the
   entire output.
4. **Boundary transfer (main open lemma):** control the change when exactly
   one endpoint lies in `A`, including information transferred through its rank
   set. Counting internal subsets alone does not control these terms.
5. **Coupled local budget:** prove `gain_t+B_(t+1)-B_t <= (1-rho)*floor(n/2)+e_t`
   for one consistent scale weighting, with total error `o(n*log n)`. Seek
   `rho>1/2`; publish any justified improvement first.

For one gate, the numbers of `k`-subsets containing both, exactly one, or neither
endpoint are `binom(n-2,k-2)`, `2*binom(n-2,k-1)`, and `binom(n-2,k)`.
The internal contribution alone gives a factor `(k-1)/(n-1)` multiplying its
information gain after normalization. Boundary terms are therefore essential.
Changes in conditioning on rank sets cannot be discarded or bounded just by
the number of possible insertion positions without a further argument.

## Reproduction

```text
lake build AKS.Kahale.FiniteFibers AKS.Kahale.AmortizedAccounting AKS.Kahale.LayerBank AKS.Kahale.RelativeOrderBank AKS.Kahale.LayerAccountingAxioms
python -B scripts/kahale_layer_bank.py --wires 3 4 5 --output docs/kahale-layer-bank-results.json
python -B scripts/kahale_relative_order_bank.py --output docs/kahale-relative-order-bank-results.json
python -B scripts/kahale_relative_order_challenge.py --output docs/kahale-relative-order-challenge.json
```
