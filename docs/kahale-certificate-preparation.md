# Preparation charges and residual sorting problems

Follow-up: [residual image difficulty](kahale-image-difficulty.md) supplies
an exact small-image completion benchmark, a joint dependency obstruction,
and limits of additive cube/gathering costs and dependency-only relaxations.

## Status

This follows the [activation-scale screen](kahale-activation-scales.md).
It establishes a derived barrier to a uniform amortized growth bound on
full conditional certificate cost, and a derived suffix bound for one
particular prefix family. These arguments are not Lean checked. Exact
Python checks support the formulas and small cases; the universal lower
bound remains 3.270559454.

The main conclusion is that paying for preparation by averaging raw
certificate growth over earlier layers is insufficient. A useful invariant
must also measure the sorting work that remains after that growth.

## 1. Repeated spikes without preparing sorted blocks

On `n=2^d` wires, build a depth-`d` recursive aligned prefix. Start with
two copies of a one-wire input; compare corresponding outputs. At each
stage compare corresponding outputs of two disjoint, identical copies of
the previous prefix. Equivalently, stage `s` compares the wire pairs that
differ only in binary index bit `s`.

Every comparator has equal scalar heights at its inputs: corresponding
copies have identical histories. At a fixed output, the two child
functions use disjoint input sets and are identical up to renaming.

Let `p` be a child's probability of zero under independent uniform input
bits, and let `c` be its minimum zero-certificate size on every zero
baseline. Initially `(p,c)=(1/2,1)`. This baseline-independent size is
preserved by the recursion, because independent identical children give

```text
AND child: (2p-p^2, c)
OR child:  (p^2, 2c).
```

The AND can be forced to zero by forcing either child to zero; when both
are zero the smaller certificate still has size `c`. The OR requires a
zero certificate in each disjoint child, hence size `2c`.

Write `K_d` for the sum of conditional zero-certificate sizes over output
wires, averaged over inputs. It is exactly `sum_outputs c p`. For comparison,
the initial value on the same `2^d` wires is `2^(d-1)`.

Exact arithmetic gives:

| Depth | Wires | Amplification over initial cost | Last layer growth |
| ---: | ---: | ---: | ---: |
| 3 | 8 | 2.071289 | 1.299632 |
| 6 | 64 | 5.062502 | 1.368653 |
| 9 | 512 | 14.018208 | 1.419478 |
| 12 | 4096 | 42.049131 | 1.451907 |

The geometric mean growth also rises; more decisively, the following
argument proves its limit is `3/2`.

### A uniform lower bound giving the asymptotic rate

The sum of `c` over output paths is `3^d`: an AND branch keeps its cost
and an OR branch doubles it. Therefore

```text
K_d = 3^d E[p_d],
```

where this expectation chooses an AND branch with probability `1/3` and
an OR branch with probability `2/3` at each step. This is cost-weighted
sampling of output paths, not uniform sampling of wires.

There is a depth-independent positive chance of keeping `p_d` near one.
Choose AND for the first three steps, an event of probability `1/27`.
Then `z=1-p` equals `1/256`. While `z <= 1/64`, its next values are
`z^2` on AND and `2z-z^2` on OR. Hence

```text
E[sqrt(z_next) | z]
  <= sqrt(z) (sqrt(1/64)/3 + 2 sqrt(2)/3)
  < sqrt(z).
```

Stop this nonnegative supermartingale at the first exit above `1/64`.
For every finite horizon, the probability of an exit is at most
`sqrt((1/256)/(1/64))=1/2`. On the complementary event `p >= 63/64`.
Consequently, for every `d>=3`,

```text
E[p_d] >= (1/27)(1/2)(63/64) = 7/384,
(7/384) 3^d <= K_d <= 3^d.
(7/192)(3/2)^d <= K_d / 2^(d-1) <= 2(3/2)^d.
```

Taking `d`th roots proves that the amortized amplification rate tends to
`3/2`. This does not assert convergence of every individual layer ratio.

Thus a universal prefix bound
`K(P) <= C poly(depth) K(initial) rho^depth`, with a fixed constant and
`rho<3/2`, is false. The same is true with any prefactor whose logarithm
is `o(depth)` along this family. A correction that remains uniformly
comparable to `K` cannot rescue such a bound. A correction that suppresses
this family's cost using its remaining sorting difficulty is still open.

## 2. A residual sorting problem survives the butterfly prefix

For this same prefix, order wire indices by inclusion of their binary
one-bit sets. Every gate compares an index with another that contains one
additional bit. Any input isotone in this Boolean lattice is fixed by
every gate and hence by the whole prefix.

Let `A` be the indices with exactly `floor(d/2)` one-bits, and put
`w=binom(d,floor(d/2))`. Fix bits below this rank to zero and bits above
it to one. The bits on `A` are completely arbitrary. Every such input is
isotone, so all `2^w` assignments survive unchanged.

The suffix of any full sorter extending this prefix must therefore sort
these `w` arbitrary bits, surrounded by fixed zero and one inputs. This
implies a suffix depth of at least `D(w)`, using the reduction below.
The central binomial coefficient is the largest of the `d+1` coefficients,
so `w >= 2^d/(d+1)`. Combining this with the existing Kahale bound gives

```text
total depth >= d + D(w)
            >= (1 + 3.270559454... - o(1)) log_2 n.
```

This coefficient **4.270559454... applies only to full sorters whose
first `log_2 n` layers are this recursive aligned prefix**. It is not a
universal improvement. It demonstrates how a prefix can create certificate
cost quickly while leaving almost the entire sorting task unfinished.

### General image-cube suffix lemma

More generally, suppose the Boolean image of a prefix contains all
assignments to a set of `w` wire positions, with the other positions fixed
to some zero/one pattern. Then every sorting suffix has depth at least
`D(w)`.

To justify removal of constants, first observe by thresholding that a
suffix sorting these Boolean inputs sorts arbitrary values in `(0,1)`
at the free positions, with the fixed values still zero and one. A gate
with two free signals is a binary comparator. A gate with one free signal
and one constant routes the free signal to a predetermined output; a gate
with two constants has predetermined outputs. Signal positions can thus
be tracked independently of free input values.

Routing may permute the free wires. Run the extracted circuit on distinct
increasing free test values, and label a free position by the rank of the
test value currently there. At every two-free gate, the actual minimum
then goes to the smaller logical label and the maximum to the larger;
one-free gates just move its label. This gives ordinary ascending
comparators on `w` logical wires, with disjoint pairs in each layer.
The final test values are sorted, so the logical output labels are in
ascending physical order and every free input is sorted by this extracted
network. Its depth is at most the original suffix depth.

This reduction is derived here, not yet a Lean lemma.

## 3. What generalizes, and what already fails

A tempting proxy is the width of the order generated by all comparator
edges. An antichain of that order supplies fixed arbitrary inputs, but
the proxy can collapse much earlier than sorting difficulty does.
For example the two equal-height layers

```text
[(0,3),(1,2)], [(0,1),(2,3)]
```

generate the chain `0<1<2<3`, despite failing to sort four inputs.
So a large fixed-input antichain is not guaranteed even in an efficient
prefix. Its output image still contains a two-dimensional Boolean cube.
We must examine the actual image, not just the accumulated comparison graph.

An exhaustive search of equal-height prefixes gives these minimum largest
axis-aligned image-cube dimensions:

| Wires | Depth 1 | Depth 2 | Depth 3 | Layer scope |
| ---: | ---: | ---: | ---: | :--- |
| 4 | 2 | 2 | 1 | All partial matchings, including idle layers |
| 5 | 3 | 3 | 2 | All partial matchings, including idle layers |
| 6 | 3 | 3 | 2 | All partial matchings, including idle layers |
| 8 | 4 | 4 | 2 | Perfect matchings only |

All searches in this table completed. The eight-wire depth-three search
has 2,555 distinct function/height states; the six-wire search has 6,596.
These are finite minima, not a general dimension inequality. In particular,
eight wires already have efficient prefixes with a smaller image cube
than the canonical butterfly's three-dimensional one.

The next precise question is a tradeoff between **image sorting difficulty**
and prefix depth or efficiency. Axis-aligned image cubes provide one
rigorous witness of residual difficulty, but may omit larger coupled
families. A proof targeting coefficient above 4 must establish a general
tradeoff; the special butterfly suffix argument alone is insufficient.
We should screen image witnesses on more general prefixes before attempting
a Lean formalization or asserting a universal residual dimension.

## Computation and reproduction

`kahale_certificate_preparation.py` uses exact rational recursion through
depth 12 (4,096 wires), independently computes truth-table certificates
through eight wires, and checks every assignment of the fixed central
antichain through 32 wires. It does not enumerate all inputs at 4,096 wires.
`kahale_fixed_antichains.py` searches actual equal-height prefixes, keeping
packed Boolean wire functions for its image-cube screen. No solver or
floating-point optimization is used in either argument's finite checks.

```text
python -B lower-bound/experiments/scripts/kahale_certificate_preparation.py --max-depth 12 --output docs/kahale-certificate-preparation-results.json
python -B lower-bound/experiments/scripts/kahale_fixed_antichains.py --output docs/kahale-fixed-antichains-results.json
```

Saved decimal growth summaries are rounded views of the exact rational
values. No Lean files were changed and no Lean builds were run.
