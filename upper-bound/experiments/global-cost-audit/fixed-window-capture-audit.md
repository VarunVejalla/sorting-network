# Shallow fixed-window capture: construction audit

Research investigation, 2026-10-10. This note supplies no new shallow network
or sorting bound. It evaluates constructions against the
[aggregate tail interface](all-scale-tail-interface.md), not an arbitrary
near-sortedness assumption. The kernel-checked coefficient remains 1770.

## The contract to implement

Fix `T=2^33`, outer fringe `f=262080`, and `epsilon=1/86000000`.
The first scramble's dyadic tails give outside-window mass less than
`(40/T)*j`. The second scramble's ideal full-column sort can have fringe escape
less than `epsilon*j/2`, according to the preceding informal argument.

For a physical repair restricted to the bottom window, define the nonnegative
defect relative to sorting that window at cutoff `f`:

```
D_F(j) = actual window escape - ideal sorted-window escape.
```

It suffices to prove, simultaneously for all supported ranks and inputs,

```
D_F(j) <= [epsilon/2 - 40/T]*j.
```

The bracket is positive but only about `1.16e-9`. It is not enough to allow
an ordinary constant relative halver error. This is a sufficient conservative
allocation, not the uniquely optimal division of the error reserve.

For small ranks already confined to the fringe before the second scramble,
ascending comparators preserve exact capture. They need not be handled as an
arbitrary sparse-compaction problem. The reflected top-window contract must
hold for the same fixed network.

Fringe and bulk repair may be composed because ascending comparisons preserve
completed prefix/suffix count guarantees. Their depths then add, and the
second operation's input promise must apply after the first. Parallelism
requires genuinely disjoint wires; separate cost estimates cannot be combined
by taking a maximum without a construction.

## Candidate 1: full window sorting

Sorting the top and bottom windows in parallel costs 561 layers. This has a
complete informal fringe count implication, but it neither supplies final
bulk accuracy nor fits the 107/19-layer budget. It remains a correctness
baseline, not an improvement to the complete sorting theorem.

## Candidate 2: a cascade of the available restricted halvers

Sixteen half-size reductions would bring `T` down to `2^17=131072<f`, leaving
output capacity slack. Even under the stronger, currently unproved promise
that each column has at most 131072 marked keys, the naive additive-error
analysis needs extremely small error per stage. Allocating `epsilon/4` across
16 stages gives

```
stage error = 1/5504000000.
```

The exact rational entropy-bound routine in
`../paterson/uniform_concentration.py` charges at least the following ceilings
for this attempted construction:

| Stage | Supported fraction relative to a half | Advertised depth ceiling |
| --- | ---: | ---: |
| First | `131072/2^32` | 6033364826 |
| Last | `1` | 257903580218 |

These are the routine's sufficient construction budgets, not network depth
lower bounds. They rule out using this available estimate as a cost certificate
for the target. Repeating a constant-error halver does not justify multiplying
errors: the same stray keys can survive repeatedly unless a contraction
interface is proved. Nor does a supported halver automatically give the
required defect bound for columns with more than its supported cohort size.

An improved compactor would need an analysis exploiting the actual distribution
and protected fringe, rather than summing uniformly tiny halver errors.

## Candidate 3: retain sorted runs and merge them

If a window arrives as sorted runs of length `2^ell`, a standard full merge
hierarchy costs

```
sum_{q=ell+1}^{33} q = (33-ell)*(34+ell)/2.
```

| Run length | Merge levels | Depth |
| --- | ---: | ---: |
| `2^29` | 4 | 126 |
| `2^30` | 3 | 96 |
| `2^31` | 2 | 65 |
| `2^32` | 1 | 33 |

The top and bottom windows can use this cost in parallel if disjoint.
The tempting 96-layer version leaves only 11 layers for any extra charged work
under a 107-layer total budget, including bulk repair. The 19-layer budget is
below even the one-level 33-layer version. Most importantly, independent row
scrambles do not supply these run premises.

## Why block-constant scrambling does not simply fix the run premise

Making the second permutation constant on each row block preserves sorted
runs within each block, but can prevent the very bulk contraction we need.
Here is a deterministic counterexample on the enlarged first-bulk state class.

Suppose the permutation is constant on the bottom block of length at least
`2*f`, and take an even number of columns. At the bulk threshold whose desired
bottom height is `f`, let half the intermediate column heights be `2*f` and
half zero. The total marked mass is `f*n` and the exact mean is `f`.

All marks lie inside that block. Its constant permutation merely permutes the
source height vector: after any full column sorting, the heights are still
half `2*f`, half zero. Hence the bulk escape is

```
f*n/2.
```

At the narrow scheduler ratio `f/m=4095/2^37`, this exceeds the target
`paperOrdinaryEpsB*m*n/2`, because

```
4095/2^37 > 1/59000000 >= paperOrdinaryEpsB.
```

For the relevant template heights, the profile satisfies the first bulk
absolute-deviation promise: its average deviation is `f`, much smaller than
`sqrt(2*(1+ln m)/m)*m`. Its rank `f*n` is above the fringe support
`delta*f*n`, so the rare-rank tail hypotheses do not exclude it.

This is a counterexample to a universal second-bulk theorem on that retained
state class, not proof that the profile is reachable after the chosen first
scramble. A run-preserving scheme needs a stronger reachability theorem or a
different mixing design. It cannot reuse the current bulk theorem unchanged.
Allowing cross-column comparator repairs would also change this argument and
must be costed explicitly.

## What an actual shallow candidate must add

The halver and run-merge candidates above do not establish a construction
inside either target budget. A subsequent [fresh-reservoir construction](fresh-reservoir-funnels.md)
uses 86 layers and meets the fringe target in fixed-input expectation at the
smaller geometry. Its universal guarantee and bulk repair remain open. The
missing interface is:

1. A multiscale contraction statement for **escaped** keys, with one fixed
   comparator network, preserved exact small-rank capture, and a bound on new
   errors. An unsupported claim that repeated halving multiplies error is
   insufficient.
2. A physical realization whose total capture and bulk depth is charged.
   At the larger geometry, this must be at most 19, which is especially tight.
3. If run reuse is used, a common-scramble theorem providing the actual run
   locations and bulk contraction. Block constancy alone fails as above.

A useful local model is a fixed fringe reservoir with surrounding dyadic
bands. Prove a comparison-step inequality for the escaped cohort and the
reservoir's available low-key capacity, then sum those inequalities against
the existing dyadic tail bounds. Counts averaged over columns do not imply
capacity in every individual reservoir; any routing between columns belongs
in the construction and depth bound.

The present evidence favors investigating such a contraction interface over
formalizing the expensive halver cascade or assuming long runs. It does not
yet justify predicting a coefficient below 1000. The complete full-sort route
and its conditional coefficient near 1485 remain separate.

## Verification scope

Existing sources and informal proofs were inspected. Depth ceilings from the
entropy routine were evaluated with exact rational arithmetic; the merge
costs are elementary arithmetic. No Lean files, tests, or builds were run.
