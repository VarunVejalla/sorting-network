# Proof plan for improving the lower-bound constant

## Decision

Seek a coefficient **above 4**, but aim first for a universal inequality
that yields *any* coefficient above `3.270559...`. The proposed bank is a
candidate, not an established route to 4.

The
[modular layer-bank investigation](kahale-layer-bank.md) records the new
accounting modules, relative-order candidate, and finite challenge results.
The [joint boundary-transfer investigation](kahale-boundary-transfer.md)
now identifies the exact conditional-information term and its proof obligations.

The most useful next mathematical object is the **weighted rank-image swap
graph**: which prefix rank states remain possible, which swapped partners
remain possible, and their actual input-fiber weights. This records the global
context that certificate minima and separate rank-slice matching discard.

We should prove its elementary counting identities before building a large
entropy formalization. The hard work is then a structural charging lemma,
not choosing numerical coefficients for the existing bank.

## Exact loss decomposition

Fix a comparator and an ordered output rank state `w`. There are only two
possible predecessor states: `w` and the state swapping its two compared
positions. Let their prefix input-fiber weights be `a,b`, allowing zero.
For uniform input rank permutations, with `N=n!`, this output contributes

\[
\frac{a+b}{N}\,h_2\!\left(\frac a{a+b}\right)
\]

bits of entropy loss, where `h_2` is binary entropy in bits. Zero total weight
contributes zero. This follows by expanding the two entropy sums after merging
the weights; it does not assume a uniform distribution on reachable outputs.

Let `A_g` be the total probability mass of output fibers having **both**
predecessors. Let

\[
V_g=\sum_{a,b>0}\frac{a+b}{N}
       \left(\frac{a-b}{a+b}\right)^2.
\]

Then the information gain `h_g` satisfies

\[
h_g\le A_g-\frac{V_g}{2\ln2},\qquad
1-h_g\ge(1-A_g)+\frac{V_g}{2\ln2}.
\]

The scalar inequality is `1-h_2(p) >= (2p-1)^2/(2 ln 2)`. An elementary proof
uses the second derivative of
`ln 2 - h_nat(p) - 2(p-1/2)^2`, which is
`1/(p(1-p))-4 >= 0`, followed by endpoint continuity.

Here “forced” means only one predecessor is possible *given the whole output
state*. It does not mean the comparator is globally redundant. The order of
disjoint gates can change individual attributions, so fix one canonical order;
the total entropy loss is unchanged and no independence assumption is needed.

These entropy identities and the scalar bound are mathematical derivations
here, not yet Lean theorems.

## What a better constant actually requires

Let `M=d*floor(n/2)` be the available comparison slots and `G` the actual
number of gates. Their information gains telescope to `log_2(n!)`, so

\[
M-\log_2(n!)=(M-G)+\sum_g(1-h_g).
\]

Thus a sufficient structural result is

\[
(M-G)+\sum_g(1-h_g)\ge\rho M-o(n\log n).
\]

It would prove leading coefficient `2/(1-rho)`. A sufficient, stronger version
uses the measurable lower bound `(1-A_g)+V_g/(2 ln 2)` in place of `1-h_g`.

| Slot-saving fraction `rho` | Resulting coefficient |
|---|---:|
| `1-2/3.270559... = 0.388483827...` | existing coefficient |
| 0.4 | 3.333333... |
| 0.45 | 3.636363... |
| 0.5 | 4 |

This is a conversion of a hypothetical saving theorem, not a newly proved
inefficiency bound. The existing depth bound already implies the first row
asymptotically; rederiving that row alone would not improve the result.

Equivalently, for target 4 define gate excess and slack

```text
E_g=max(h_g-1/2,0),   S_g=max(1/2-h_g,0).
```

The target charging statement is

\[
\sum_g E_g\le\sum_g S_g+\tfrac12(M-G)+o(n\log n).
\]

The potential in [the target-four note](kahale-target-four.md) is one possible
way to produce this statement by charging excess against changes in a bank.
The endpoint-controlled bank alone supplies no such charge.

## Proof sequence and current status

### 1. Reconstruct inputs from decisions — completed

[ComparisonTrace.lean](../AKS/Kahale/ComparisonTrace.lean) now defines the
comparator swap trace and its reverse reconstruction. It proves:

- a strict ordered comparator output has exactly the two candidate predecessor
  vectors described above;
- the trace length equals the number of comparators;
- reversing a genuine trace recovers the input;
- output plus trace determines the input injectively.

These are general theorems for any linearly ordered value type, not finite
examples. They are the combinatorial foundation for rank-fiber counting.

### 2. Formalize fiber accounting — next routine proof work

For `rankFiberSize`, prove the exact one-comparator merge identity

```text
fiber(pre ++ [c], w) = fiber(pre,w) + fiber(pre,swap_c(w))
```

when `w(c.i)<w(c.j)`. Prove zero fibers for reversed outputs and preserve
injectivity of ranks. The two predecessor families are disjoint. Then prove
the entropy-sum identity from finite counts, using `0 log 0 = 0`.

Useful dependencies already exist: rank-fiber definitions in
[RankInformation](../AKS/Kahale/RankInformation.lean), input reconstruction,
rank injectivity, and Mathlib's binary-entropy upper bound and derivative.
For the quadratic imbalance bound, use the elementary second-derivative proof
above rather than introducing external trust.

**Acceptance condition:** recover the usual one-bit-per-gate bound and exact
small rank-fiber examples without silently replacing weighted distributions
by uniform image distributions. This proves the accounting, not a new constant.

### 3. Discover a structural charging lemma — principal open problem

A high-information comparator needs both predecessor orientations to be
reachable with nearly equal weights. Study how often a sorting network can
create and retain that weighted swap symmetry while growing its certificate
families and satisfying all rank requirements.

Try to construct a charge from the excess of such gates to:

- earlier gate slack, where orientations were forced or unequal;
- unused comparison slots while large independent structures were prepared;
- a bank change representing creation or consumption of coherent ambiguity.

A charging construction must establish both its coverage of excess and a
bound on how many gates charge the same resource. Input-boundary or terminal
exceptions need a proved total `O(n)` or `o(n log n)` budget. Repeatedly using
the same witness or labeling a logarithmic number of layers “exceptional”
without accounting for their cost is invalid.

The existing `C=L-2I` and total correlation `T` are candidates for this bank.
If neither controls the charge, add conditional correlations or certificate
overlap information, or change the bank. This step is a substantial new
mathematical argument; the preceding identities do not make it routine.

### 4. Challenge the lemma on analytic families before committing to it

Use growing families whose relevant fibers can be counted exactly:

- independent sorted blocks and comparisons of their extrema;
- layers producing large certificate growth with little joint information;
- near-terminal balanced ambiguities, which can still lose a full bit;
- full-reachability suffixes, where independent Hall constraints are vacuous.

The block-maxima calculation `k/(2k-1)` is a useful benchmark, but not a
universal consequence of certificate size. Its excess over half a bit tends
to zero; the finite counterexamples show other prefixes behave differently.

Small exhaustive catalogues should expose false local lemmas and missing
statistics. They cannot establish an asymptotic rate. Sampling whole rank
outputs at large `n` is particularly unsuitable for estimating their entropy:
rare fiber collisions may be missed. Use exact combinatorial counts or proved
analytic distributions for scaling claims.

**Stop condition for a candidate:** if its exceptions or endpoint bank cost
can be `Theta(n log n)`, it does not prove 4. Refine or abandon that candidate
before spending effort formalizing its entropy infrastructure.

### 5. Assemble the strongest proved coefficient

Once a universal saving fraction or amortized budget has been obtained,
formalize its quantitative error and combine it with the finite entropy
telescoping theorem and `log_2(n!)=n log_2 n-O(n)`.

Publish any coefficient above the current one when justified; continue toward
4 using the same explicit saving parameter. Do not add the information-count
bound to the Fibonacci bound unless an actual coupled inequality supports it.
Their separate maximum remains the existing coefficient.

## Additional bank-analysis safeguards

- `C` can have either sign; its initial and final values are zero, but its
  intermediate magnitude is not controlled by those endpoint facts.
- For time-varying weights, include the entire difference `B_(t+1)-B_t`.
  Terms such as `(beta_(t+1)-beta_t)*C_(t+1)` cannot be discarded.
- Initial weights multiplying `T_0=O(n)` must preserve a subleading endpoint
  cost. A coefficient growing like `log n` can destroy the intended bound.
- Do not define a bank using the unknown desired depth bound and then treat
  its endpoint control as an independently proved property.

## Finite diagnostic update

The exact catalogue now records forced mass, ambiguous mass, squared
orientation imbalance, and the range of information gains for identical
incoming certificate pairs. On five wires, the signature `(2,3),(2,3)` can
have information gain from approximately `0.39001345` to `1` bit. The signature
`(3,2),(3,2)` has the same observed range. Thus these minima alone do not
determine the conditional fiber behavior required by the charging lemma.

[Updated results](kahale-rank-entropy-results.json) come from exact finite
rank counts; entropy values are numerical. The new trace and predecessor
lemmas are kernel checked separately. No higher coefficient is claimed.

## Recommended immediate work

The exact rank-fiber merge identity is now proved in
`AKS/Kahale/RankFiberMerge.lean`. Use weighted swap closure
to formulate one falsifiable charging lemma with a fully specified exception
budget. Investigate that lemma on analytic block families before expanding
the formal entropy library or tuning potential weights.

The [sorted-block calculation and charging conjecture](kahale-swap-charging.md)
show why the bank must account for collective swaps: a parallel layer can
gain more information than the sum of its initial single-gate gains.

## Verification and reproduction

The focused build succeeded for `AKS.Kahale.ComparisonTrace` and
`AKS.Kahale.ComparisonTraceAxioms`. The guarded audits for strict comparator
preimages, trace reconstruction, and output-plus-trace injectivity use only
`propext`, `Classical.choice`, and `Quot.sound`.

```text
lake build AKS.Kahale.ComparisonTrace AKS.Kahale.ComparisonTraceAxioms
python -B scripts/kahale_rank_entropy.py --output docs/kahale-rank-entropy-results.json
```

This was a focused build of the lower-bound additions, not a verification of
the concurrently changing upper-bound development.
