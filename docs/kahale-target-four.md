# Target 4: certificate progress and coherent rank information

## Research target and status

The [proof plan](kahale-proof-plan.md) now gives the loss decomposition,
coefficient conversion, proof obligations, and stop conditions. Comparator
trace reconstruction and the two-predecessor lemma have been implemented as
the first general foundation.

The user originally set **4** as the desired asymptotic lower-bound coefficient for
`D(n)/log_2 n`. We are treating it as a target, not an established bound or an
evidence-based prediction. The proved coefficient remains `3.270559...`.

The target now preferably exceeds 4. The
[modular layer-bank investigation](kahale-layer-bank.md) keeps the saving
fraction as a parameter and records finite obstructions to two simple banks.

This investigation replaces independent rank-slice matching with the joint
distribution of whole rank permutations. It identifies an amortized potential
with controlled endpoints and rules out two tempting pointwise inequalities.
The crucial amortized inequality is **not proved**.

## Exact information accounting

Let `X` be a uniform random input rank permutation. After layer `t`, let
`Y_t` be the entire output rank vector and `H_t=H(Y_t)` its Shannon entropy
in bits. A sorting network has

```text
H_0 = log_2(n!),    H_d = 0.
```

The distribution of `Y_t` generally is not uniform on its image. Rank fibers
must be counted, rather than replacing entropy with the logarithm of image
size. Each layer's joint entropy loss is exactly the conditional entropy of
its predecessor given its output. A layer of `m` comparators loses at most
`m` bits because every output has at most `2^m` predecessor orientations.

That familiar bound gives only coefficient 2. To obtain coefficient 4 by
information accounting, a sufficient result is

\[
H_t-H_{t+1}\le\frac n4+B_t-B_{t+1}+e_t,
\]

with `B_0-B_d=O(n)` and total error `sum e_t=o(n log n)`. Summing would give

\[
\log_2(n!)\le\frac{nd}{4}+o(n\log n),
\qquad d\ge(4-o(1))\log_2 n.
\]

The `n/4` budget is half the maximum comparison slots available in a layer.
This is not the stronger assertion that every actual comparator loses at most
half a bit. Early or terminal exceptional layers with total excess `O(n)` are
consistent with the target.

## An endpoint-controlled bank

Let `z_i(t),o_i(t)` be the exact minimum zero/one certificate sizes and set

\[
L_t=\sum_i\log_2(z_i(t)o_i(t)),\qquad
I_t=H_0-H_t,\qquad C_t=L_t-2I_t.
\]

Initially `z_i=o_i=1`, so `C_0=0`. At the sorted endpoint,

\[
z_i=i+1,\quad o_i=n-i,\quad
L_d=\log_2\prod_i(i+1)(n-i)=2\log_2(n!).
\]

Hence **`C_d=0` exactly**, as well. This bank compares certificate progress
with actual information gained, retaining both quantities at intermediate
cuts without introducing a leading-order endpoint penalty.

Also define total correlation

\[
T_t=\sum_i H(Y_{t,i})-H_t.
\]

Its initial value is `n log_2 n - log_2(n!)=O(n)`, and its final value is zero.
Thus a candidate bank is

\[
B_t=\beta_t C_t+\gamma_t T_t,
\]

with bounded initial `gamma_0`; nonlinear functions of the same statistics
could also preserve the endpoint property. `C_t` can have either sign. A proof
cannot assume nonnegativity, and the endpoint property alone supplies no
stage inequality.

For a fixed `beta` and `gamma=0`, the amortized layer charge becomes

\[
(H_t-H_{t+1})+\beta(C_{t+1}-C_t)
=(1-2\beta)(H_t-H_{t+1})+\beta(L_{t+1}-L_t).
\]

This exposes the intended tradeoff between rank information and certificate
growth. It also exposes a limitation: the first full layer has entropy loss
`n/2` and certificate log-growth `n`, so its charge is `n/2` for every fixed
`beta`. A uniform bound of `n/4` with this bank fails immediately. A valid
asymptotic proof must allow an `O(n)` initial excess, use additional correlation
or structural terms, or change its weights with the remaining depth.

These identities and the entropy reduction above are mathematical derivations
in this document. They are not new Lean entropy theorems.

## What the exact finite computation rules out

[kahale_rank_entropy.py](../lower-bound/experiments/scripts/kahale_rank_entropy.py) enumerates actual
reachable Boolean network states on three through five wires, and propagates
the exact counts of all input rank permutations. Boolean wire functions
determine rank behavior because execution commutes with every rank-threshold
map; the rank vector is determined by those threshold outputs. Therefore the
rank distribution is independent of which prefix represents a reachable
Boolean state.

Counts are exact; the script evaluates entropies numerically from the counts.
The catalogue sizes are 11, 261, and 43,337 states, respectively.

### Large certificates do not force low local information gain

On four wires, take the prefix

```text
(0,1), (0,2), (0,3), (2,3), (1,2).
```

Wires 2 and 3 both have exact certificate pair `(3,1)`. The 24 rank inputs
produce exactly two output rank permutations, each with fiber size 12.
The comparator `(2,3)` merges them into the identity output, so its entropy
loss is exactly **one bit**.

For contrast, comparing the maxima of two disjoint internally sorted blocks
of size `k` loses `k/(2k-1)` bits, approaching one half. That formula follows
because the two predecessor orientations are both possible precisely when
the two largest ranks belonged to different blocks, an event of probability
`k/(2k-1)`. Their equal fiber weights make the conditional entropy one bit
on that event and zero otherwise.

The block formula is correct for that special prefix, but **not** a universal
bound from minimum certificate size alone. The four-wire example has `k=3`
and loss 1, exceeding `3/5`.

### A large certificate sum does not force a low layer loss

Another four-wire prefix is

```text
(0,1), (2,3), (0,3), (1,2).
```

The wire certificate pairs are `(1,3),(1,3),(3,1),(3,1)`: every sum is `n`.
Its four rank output fibers have sizes `8,8,4,4`. The parallel layer
`[(0,1),(2,3)]` sorts all ranks and loses

\[
H(1/3,1/3,1/6,1/6)=\log_2 3+1/3
=1.918295834\ldots\text{ bits},
\]

which exceeds the raw `n/4=1` budget. This rules out that pointwise criterion,
not an amortized bound with a bank or a finite-size correction.

Both sets of exact certificate and rank-fiber facts are kernel evaluated in
[RankInformation.lean](../lower-bound/experiments/AKS/Kahale/RankInformation.lean). The focused build
and [separate axiom audit](../lower-bound/experiments/AKS/Kahale/RankInformationAxioms.lean) passed,
with dependencies only `propext`, `Classical.choice`, and `Quot.sound`.
The real-valued entropy consequences are the calculations here, not additional
formalized entropy inequalities.

## The actual proof obligation

We need a universal amortized tradeoff, not another pointwise penalty based on
certificate minima. For example, layers with high information gain must either
consume a bank accumulated earlier, use relatively few comparison slots, or
leave structural obligations that make subsequent layers less efficient.

The joint rank distribution captures compatibility across all threshold
slices. Minimum certificate sizes still summarize only part of the structure;
if `C_t` and `T_t` cannot support a closed inequality, the bank will need
conditional correlations, certificate-family overlaps, or a hierarchy of
rank-conditioned statistics. No closure or half-slot average bound has yet
been shown.

The finite counterexamples do not establish an asymptotic barrier at 4.
Conversely, the endpoint-controlled bank is a formulation of a possible proof,
not evidence that the required inequality is true. The next useful result is
an amortized inequality with a quantified error, or an obstruction to a
specific candidate bank, before predicting any improved coefficient.

## Reproduction

```sh
python -B scripts/kahale_rank_entropy.py --output docs/kahale-rank-entropy-results.json
lake build AKS.Kahale.RankInformation AKS.Kahale.RankInformationAxioms
```

[Machine-readable results](kahale-rank-entropy-results.json) include the
extremal gate and layer prefixes and exact rank-fiber histograms.
