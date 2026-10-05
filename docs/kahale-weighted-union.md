# Weighted pairwise union costs: first closure attempt

## Status

We have a universal closed **upper** update bound using only per-wire and
pairwise certificate costs. Its certificate-cover witnesses are formalized in
[PairUnionRecurrence.lean](../AKS/Kahale/PairUnionRecurrence.lean).
The complete numerical recurrence and weighted-potential consequences below
are mathematical derivations, not additional Lean theorems.

No improvement over the lower-bound coefficient `3.270559...` is established.

## A closed upper recurrence

Let `z_i` and `o_i` be the minimum zero/one certificate sizes at wire `i`.
Let `Z_ij` be the minimum size of a certificate forcing both wires zero,
and `O_ij` the minimum size forcing both wires one. Set `Z_ii=z_i`, `O_ii=o_i`.
These are the union costs previously recorded: zero certificates of the OR
and one certificates of the AND.

For a comparator on `(i,j)`, with min output at `i`, and any other wire `k`,

```text
Z'_ik = min(Z_ik, Z_jk)
Z'_jk <= min(n, Z_ik + z_j, Z_jk + z_i, Z_ij + z_k)

O'_jk = min(O_ik, O_jk)
O'_ik <= min(n, O_ik + o_j, O_jk + o_i, O_ij + o_k).
```

For the gate's own pair, `Z'_ij=Z_ij` and `O'_ij=O_ij`. The new diagonal
entries are exactly

```text
z'_i=min(z_i,z_j), z'_j=Z_ij,
o'_i=O_ij,        o'_j=min(o_i,o_j).
```

Why the inequalities hold: a certificate forcing `i,k` zero, united with
one forcing `j` zero, forces all three zero and has size at most
`Z_ik+z_j`. Choose the other two possible pairs to obtain the other bounds.
The one-certificate argument is identical. The equalities for the min/max
outputs use the exact certificate-family identities and distributivity.
The full-input certificate supplies the cap `n`.

The formal theorems `triple_zero_certificate_cover` and
`triple_one_certificate_cover` establish the union witnesses and size bounds;
`max_zero_certificate_pair_cover` and `min_one_certificate_pair_cover`
connect those witnesses to a comparator output. They retain the third wire
at the prefix; the recurrence uses the fact that the gate leaves it untouched.

Process disjoint comparators sequentially to obtain an upper matrix for a
whole layer. Every expression is monotone in the incoming costs, so previously
computed upper bounds remain safe. This closes an upper-bound recurrence
without storing triple unions; it does **not** make exact updates determined
by pairwise costs.

## Weighted potential

For nonnegative weights, define

\[
P_s=\sum_{i<j}w_s(j-i)(Z_{ij}+O_{ij}).
\]

The upper matrix gives a universal, generally nonlinear bound on `P_(s-1)`
in terms of the old pair matrix. Sorting completion additionally restricts
active comparator width to `2^s-1` when `s` layers remain before this layer.
Reducing this matrix bound to a useful scalar potential inequality remains
the difficult step.

The experiment uses three weight choices:

```text
uniform:               w_s(g)=1
inverse distance:      w_s(g)=1/g
suffix capped distance:w_s(g)=min(1,2^s/g).
```

For exact finite multiplier measurements, we only admit transitions whose
output has an actual sorting completion in at most `s-1` layers, found from
the exhaustive state graph. This completion oracle is stronger than the width
condition and is unavailable at general arity. Its measured maxima therefore
cannot serve as universal asymptotic multipliers.

## An obstruction for the simplest scalar iteration

For uniform weights, the initial potential is `2n(n-1)`. At the sorted
endpoint, `Z_ij=j+1` and `O_ij=n-i`, hence

\[
P_{\mathrm{sorted}}=\frac23 n(n^2-1),\qquad
P_{\mathrm{sorted}}/P_{\mathrm{initial}}=(n+1)/3.
\]

On even `n`, a first layer comparing disjoint input pairs has potential
`3n^2-4n`. Thus any uniform, arity-independent stage multiplier must be
at least `3/2`, giving at best the leading coefficient

\[
1/\log_2(3/2)\approx1.709511.
\]

This excludes only the scheme that repeatedly applies one uniform multiplier
to this particular sum. It does not exclude a remaining-depth-dependent or
matrix-sensitive argument.

The suffix capped weights introduce another issue. When `d >= ceil(log_2 n)`,
the initial weights are all one, but the terminal weights are `1/g`.
Writing `H_(n-1)` for the harmonic number, the terminal potential is

\[
(n+1)(nH_{n-1}-(n-1))+n(n-1)/2.
\]

Its ratio to the initial potential is only `Theta(log n)`. Small measured
stage multipliers are therefore not, by themselves, evidence of a stronger
depth bound: these weights have also removed a factor of `n` from the required
total growth. Multiplying each `P_s` by a time-dependent normalizing constant
does not change this issue, since the normalization telescopes in the final
bound. Different weights or a sharper comparison argument may still help.

## Exact finite findings

| Wires | Reachable states | Exact pair-matrix signatures | Largest sum of pair-cost overestimates in one layer |
|---|---:|---:|---:|
| 3 | 11 | 7 | 0 |
| 4 | 261 | 44 | 4 |
| 5 | 43,337 | 581 | 9 |

The recurrence bounds every matrix entry in every enumerated transition.
Repeated identical transition summaries are evaluated only once; this does
not change the maxima or coverage of distinct numerical cases.

On five wires, selected maximum multipliers for transitions admitting a real
sorting completion within the budget are:

| Weight | Layers remaining before layer | Actual maximum | Closed upper maximum |
|---|---:|---:|---:|
| Uniform | 1 | `40/37` | `85/74` |
| Uniform | 2 | `74/65` | `6/5` |
| Inverse distance | 1 | `582/553` | `622/553` |
| Inverse distance | 2 | `553/479` | `292/241` |
| Suffix capped distance | 1 | `291/385` | `311/385` |
| Suffix capped distance | 2 | `77/78` | `407/390` |

The suffix capped potential can decrease even while the network progresses
toward sorting. This is consistent with its changing endpoint scale above.
For two remaining layers its actual maximum is below one, while the closed
bound's maximum is above one: an example of information lost in the cover bound.

Interestingly, exhaustive enumeration finds **no** two prefixes with identical
full pair matrices whose same next parallel layer produces different full
pair matrices, through five wires. Thus the pair matrix determines its next
matrix on each of these finite catalogues, even though the generic upper
recurrence is not exact. This observed closure at small arity is stronger than
merely retaining minimum remaining depth. It is not a general closure theorem.

A separate seeded sample of 20,000 six-wire prefixes likewise found no
nonclosure witness. Including the single-gate continuations examined, it
encountered 11,420 distinct pair-matrix signatures. This sample is not
exhaustive and does not establish closure on six wires.

The focused build `lake build AKS.Kahale.PairUnionRecurrence AKS.Kahale.Axioms`
passed, including guarded axiom checks for the four new witness theorems.
Their dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
The existing lower-bound proof was not strengthened by these lemmas.

## Reproduction and next question

The [global rank-congestion follow-up](kahale-rank-congestion.md) now
formalizes a coalition capacity condition and exhibits a 12-wire obstruction
missed by every proper subcoalition of that witness. This moves the investigation
to simultaneous rank requirements; no improved coefficient is established.

```sh
python -B scripts/kahale_weighted_union.py --wires 3 4 5 --sample-six 20000 --output docs/kahale-weighted-union-results.json
```

The [exact results](kahale-weighted-union-results.json) record finite actual
multipliers, the corresponding closed upper multipliers, and any pair-matrix
nonclosure witness. Arithmetic is exact; this enumeration is not kernel checked.

The next useful target is an overlap-sensitive correction to this upper
recurrence that preserves an endpoint growth ratio polynomial in `n` while
charging unavoidable loss over logarithmically many layers. The current
pair-plus-single cover bound deliberately discards overlaps, so it cannot
alone supply such a charge.

The observed finite closure gives a more specific lead: investigate whether
the exact pair-matrix update has a universal formula, or find its first
counterexample. An exact or tighter update would let us study weighted
potentials without the demonstrably avoidable loss in the cover recurrence.
