# Oblivious concentration and exact first-split repair

Status: informal constructive argument and scalar experiment, 2026-10-10.
No new sorting theorem is claimed. This concerns the first split only; the
remaining three partition levels need separate construction and accounting.

Follow-up: [sparse concentration and pool selection](sparse-concentration-and-pool-selection.md)
reduces the layout estimate below from 33 to one matching layer and explores
cheaper adaptive half-halvers. The original numerical example below is retained
as the baseline, with that layout estimate superseded.

## An exact concentration lemma from supported separators

Consider a bag known to belong to the lower native half, containing at most
`K` wrong-half keys. These keys are its largest keys. For an upper-half bag,
they are its smallest keys. Thus the existing supported separator applies
without comparing against an explicit rank threshold.

Suppose `K <= sigma*m`, with support `sigma`, fringe size `f`, error `e<1`,
and separator depth `s`. Apply the separator and split its output into:

- The appropriate extreme fringe, containing at most `K` wrong keys.
- Its complement, containing at most `floor(e*K)` wrong keys.

Recursively concentrate each part with its corresponding budget. Both child
networks run in parallel. If a budget is zero, leave that block untouched and
declare it pure. If support no longer holds, declare the whole block part of
the repair core. The stopping decisions depend only on sizes and certified
budgets. The resulting core is therefore a fixed set of wires.

Induction proves that **every** wrong-half key lies in this fixed core.
This does not identify those keys individually; the core may also contain
many correct keys. For core cardinality `F` and depth `H`, the recurrence is

    F(m,K) = F(f,K') + F(m-f,floor(e*K)),
    H(m,K) <= s + max(H(f,K'), H(m-f,floor(e*K))),
    K' = min(K,f).

Use `F(m,0)=0`; a nonzero unsupported leaf has `F(m,K)=m` and depth zero.
Size decreases at each nonterminal node, so the recursion terminates.

The complement's surviving wrong keys are still an extreme cohort of its
own input, which justifies applying the same contract there. In contrast,
reapplying a separator to the original whole bag only proves `e*K` leakage
again: captured keys can re-enter. It does not justify `e^t*K` leakage.

## Compatibility with the existing primitive

For the completed separator, `sigma=1/50`,
`e=9978053/227625354`, and `s=989`. It accepts sizes divisible by 32 and
guarantees fringe `m/32`. Enlarge that fringe to

    f = 32 * ceil(m/1024).

Both recursive blocks then have size divisible by 32. Enlarging a fringe
can only reduce leakage. Stop when `m<=32`, support fails, or the fringe
would consume the entire block. This avoids silently assuming an all-size
primitive or padding keys that change the native-half counts.

This extracts an actual candidate construction from the current supported
contract, though its recursive implementation and induction have not been
formalized in Lean.

## Exact repair after concentration

Run all shallow-bag concentrators in parallel. Include their fixed cores,
the root bag, and cold storage in a repair pool. Every remaining wire has a
known native-half label inherited from its bag. Deep wires were already pure.

The upper region contains exactly `|U|/2` keys of each native half, by the
existing root prefix count and deep-half purity. Consequently the number
of lower-half keys needed in the pool is the fixed integer

    a = |U|/2 - number of certified-pure lower-half wires outside the pool.

Exactly partition the pool into its smallest `a` keys and the rest. Full
sorting is sufficient. It follows that every output wire now has a fixed,
input-independent native-half label.

**Layout is an additional obligation.** These labeled wires need not already
occupy the existing positional halves `B(1,0)` and `B(1,1)`. They must be
routed there by an oblivious comparator network; arbitrary output rewiring
is not automatically free in the current model.

A sufficient adapter uses the existing known-permutation correction: choose
a representative distinct-rank input matching the fixed binary label pattern,
then construct its sorting network of depth at most `k` on `2^k` wires.
Thresholding commutes with comparator execution, so that network sends every
input with the same binary label pattern to the correct halves. For arbitrary
`|U|`, a proof via padding/restriction gives a candidate cost
`ceil(log_2 |U|) <= 33`; this local variant still needs an explicit adapter.
The route must be confined to `U`. None of this replaces the later nested-bin
partition requirements.

Thus an illustrative first-split budget is

    concentration depth + exact pool-partition depth + layout depth.

## Scalar experiment with current parameters

Run `python upper-bound/experiments/paterson/concentration_budget.py`.
At maximal root capacity, using rounded bag-size upper budgets, it reports:

| Bag level | Size budget | Wrong-key budget | Fixed core | Sequential rounds |
|---:|---:|---:|---:|---:|
| 2 | 13,541,632 | 4727 | 16,160 | 5 |
| 4 | 305,532,160 | 32 | 448 | 6 |

Including four level-2 cores, sixteen level-4 cores, and root/cold storage,
the pool budget in this example is **678,745**. A bitonic sorter has depth
at most **210**, because this fits below `2^20`. Concentration costs six
sequential primitive calls in the longest branch. With the existing primitive,
the example costs `6*989 + 210 = 6144` before layout, or up to 6177 including
the proposed layout adapter. This is substantially worse than the existing
561-layer complete root-region sort.

These are scalar calculations for the displayed sizes, not a uniform theorem
over all admissible bag sizes. Actual sizes may be smaller; the rounded
recurrence has not been proved monotone in size. A uniform cost theorem must
bound every allowed size or establish an appropriate monotone envelope.

## What this resolves, and what remains

The small-error supported interface does allow exact concentration by recursive
pruning, without a magical key-identification operation. But the **current
implementation is much too expensive** to be an improvement.

Even with a substantially cheaper separator of depth `s`, this example's
first-split cost is approximately `6s+243` using full pool sorting and the
layout adapter. At `s=30` it is 423 before the remaining three partition
levels. The full-sort pool baseline alone precludes repair costs in the tens.

Two concrete opportunities remain:

1. Construct a much cheaper **one-sided** supported extreme-cohort primitive.
   This concentration argument does not require the large-cohort first-split
   contract or both tails simultaneously. Its cost should be audited separately
   from the complete 989-depth separator.
2. Exploit the pool's structure or construct exact arbitrary-cut partitioning
   directly, rather than fully sorting the approximately 679,000-key pool.
   The unconstrained root/cold portion means that this is still a substantial
   selection problem; concentration alone does not solve it.

The next useful lemma is the formal recursive concentration contract with
fixed core/locality/depth, parameterized by a one-sided primitive. The next
useful cost investigation is that primitive's feasible depth together with
an exact pool partitioner. Until both are available, this route supports no
improved global coefficient, let alone 200.
