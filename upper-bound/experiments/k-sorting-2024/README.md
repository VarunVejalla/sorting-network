# 2024 k-sorting paper: first relevance screen

Status: literature screen, 2026-10-10. No improved binary sorting bound is
claimed. The active research ticket is [UB-08](../../backlog/high-upside-architecture.md).

## What the paper proves

Dobrokhotova-Maikova, Kozachinskiy, and Podolskii, *Towards Simpler Sorting
Networks and Monotone Circuits for Majority* (APPROX/RANDOM 2024), studies
high-arity comparators that sort all entries in a block. Its Theorem 2 gives a
k-sorting network of depth at most `(2 + o(1)) (log_k n)^2` when
`log k = ω(log log n)`. The exponent 2 is a square on the logarithm. This is
not a bound for ordinary binary-comparator depth.

The main transferable idea is its **s-sorted** invariant (Definition 16): on
Boolean inputs, all zeros precede one contiguous interval of length at most
`s`, and all ones follow it. Correctly placed extreme values remain in place
under later comparator operations. Lemma 18 shows how one high-arity layer can
merge `p` such arrays into an `(s p + 2 n p/t)`-sorted array using comparators
of arity at most `t p` (with a slightly better bound under divisibility).
Lemma 19 builds an s-sorter in `ceil(log_t n)-1` high-arity layers, where
`t=floor(sqrt(k))`, with `s <= 2 ceil(log_t n) n/t`.

This localized-disorder invariant is potentially relevant to the project's
partial-sorting ticket UB-04. It may let a separator carry a controlled
uncertain interval rather than requiring every intermediate column to be
exactly sorted. The paper's own construction, however, uses high-arity
comparators and a different global recurrence. The current Chvatal counting
lemmas assume exactly monotone columns; they do not automatically absorb an
uncertain interval.

## Binary-cost screens

Replacing each k-comparator independently by a binary sorter of depth `S(k)`
multiplies the layer count by `S(k)`. For the full Theorem 2, if `k=n^α` and
`S(k) <= C log₂ k + O(1)`, the resulting coefficient is about `2C/α`, at
least `2C`. With the current `C=1419` this does not improve the endpoint.
Using Batcher as the local sorter gives quadratic-log depth in this regime.

For the finite current column width `n=2^43`, Lemma 19 can be screened more
directly. If `k=2^r`, `t=2^floor(r/2)`, and
`d=ceil(43/log₂ t)`, then its high-arity partial-sort layers cost
`(d-1) r(r+1)/2` binary layers when each comparator is implemented by a
bitonic sorter. The interval guarantee is at best `s/n <= min(1, 2d/t)`.
Some representative parameters are:

| `r` | `t` | partial-sort depth | guaranteed `s/n` |
| ---: | ---: | ---: | ---: |
| 16 | 256 | 680 | 0.0469 |
| 20 | 1,024 | 840 | 0.00977 |
| 24 | 4,096 | 900 | 0.00195 |
| 32 | 65,536 | 1,056 | 0.0000916 |

If every uncertain bit is charged as a defect, the current ordinary-node
bulk tolerance of `1/59,000,000` is much smaller than these interval fractions.
A coarse scan over power-of-two
arities, followed by bitonic sorting of the remaining interval, did not beat
the depth-946 bitonic full sorter on `2^43` wires; the best screened total was
about 1,072 layers and came from a trivial interval bound. This is only a
screen of the direct Lemma 19 + independent binary sorter route, not a lower
bound on what the paper's structure can achieve.

## Useful next test

Do not formalize the whole high-arity construction yet. First ask whether the
current two-round separator can use an s-sorted column contract at all. A
precise bridge would need to bound how the uncertain intervals affect the
bulk rank count and shared fringe event after row scrambling, with an error
budget compatible with the actual `NodeSpec`. If that bridge still requires
`s/m` near `1/59,000,000`, the published Lemma 19 parameters are unlikely to
help directly. If a weaker invariant tolerates much larger localized defects,
the paper's merge lemma may offer a useful template for a new local stage.

Source: [paper PDF](https://kozmath.github.io/papers/upper_bounds.pdf),
[LIPIcs DOI](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2024.50).
