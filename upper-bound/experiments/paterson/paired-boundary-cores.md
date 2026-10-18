# Paired boundary cores: exact error identity and composition constraints

Status, 2026-10-10: informal two-block theorem and exact scalar arithmetic.
Uniform concentration costs remain conditional on the unformalized adapters
listed in the uniform audit. No improved global network has been proved.

## Two-block theorem

Let ordered physical blocks `L,R` each have `m` wires, and let `theta` be a
rank threshold. Suppose their union contains `m+Delta` keys below `theta`.
Select fixed cores of sizes `fL,fR`, without exchanging values between the
blocks during concentration. Outside the cores, let:

    a = # high keys in L outside its core,
    b = # low keys in R outside its core.

Sort the union of the two cores in increasing physical order. Its first
`fL` outputs belong to the left core and the remaining `fR` to the right
core. This uses a fixed quota, not an input-dependent cut.

The final error counts are exactly

    left high errors = max(a, b-Delta),
    right low errors = max(b, a+Delta).

Proof: outside the cores there are `m-fL-a` left low keys and `b` right low
keys. Thus the combined core contains `fL+Delta+a-b` low keys. After sorting,
its left high count is `(b-a-Delta)_+` and right low count is
`(Delta+a-b)_+`. Add the respective outside-core errors. Feasibility of the
actual core low count automatically supplies the cardinality bounds.

In particular, for a balanced pair (`Delta=0`), each side has exactly
`max(a,b)` remaining errors. If each concentrator leaves at most `epsilon*K`
outside, the paired repair has that same residual bound, **not twice it**.
No initially pure reservoir is required.

If both concentrations are exact, the remaining errors are precisely
`(-Delta)_+` left and `Delta_+` right. A pair-local operation cannot remove
that imbalance without exchanging keys with other blocks.

The theorem also holds for unequal block sizes with the quota `fL` and
`Delta` defined relative to the left block's cardinality. Sorting can use
the existing arbitrary-size bitonic network. A max/min singleton tournament
on each side followed by one comparison is a concrete balanced base case.

## Primitive contract and cost

Require one-sided concentration of left high and right low cohorts into
fixed cores, with specified outside residual bounds. The wrong keys are
extreme cohorts of their respective block, so supported-halver concentration
is applicable when its support and arity assumptions hold. Both directions
execute in parallel because they act on disjoint blocks.

With concentration depths `HL,HR`, a sufficient pair depth is

    max(HL,HR) + bitonicDepth(fL+fR).

For ordered physical blocks, no additional layout layer is necessary: the
scattered core sort already has the desired left/right quota. Arbitrarily
interleaved stored bags still need an orientation/layout adapter; this cannot
be inferred from the value-set calculation.

`paired_core_budget.py` evaluates exact-concentration envelope costs for
equal blocks of size at most 305,532,147:

| Wrong-key budget per side | Uniform core per side | Concentration | Joint core sort | Total pair depth |
|---:|---:|---:|---:|---:|
| 1 | 1 | 29 | 1 | 30 |
| 32 | 6,122 | 190 | 105 | 295 |
| 4727 | 2,138,629 | 185 | 276 | 461 |
| 6,080,089 | 168,917,608 | 180 | 435 | 615 |

These are generic scalar pair bounds. They are not assertions that the
corresponding actual Paterson bags have equal sizes or balanced counts.
The dense finest-bin contaminants remain expensive. Even the conservative
32-key case exceeds the earlier 117-layer suffix margin if paid sequentially
after the uniform first-split construction.

Approximate concentration may trade smaller cores for nonzero `a,b`; the
identity above makes that trade precise. One must certify the **total**
residual count over all unselected frontier blocks, not merely a per-path
budget. Pruning many branches at a small nonzero budget can accumulate larger
total residuals.

## Why local balance is not automatic in the actual forest

For two adjacent native intervals, the union's actual lower-half count can
differ from the left capacity because some keys lie in other bags, the pool,
or deeper subtrees. The existing stranger invariant bounds such differences
but does not force `Delta=0`. Complete upper-half balance holds at the root's
main split; it does not imply balance for every adjacent level-4 pair.

Using the balanced pair theorem at every boundary would silently assume the
very prefix-count control that the previous audit found missing. A valid
scheduler must move count imbalances as well as reduce residual contamination.

## What is monotone under overlapping ordered repairs?

For any threshold, sorting a combined core and assigning its smallest keys
to the earlier block can only **increase** the number of low keys in that
block. Thus at every positional prefix lying between the repaired blocks,
the total low-key count cannot decrease; prefixes containing both or neither
are unchanged. Consequently the threshold crossing count

    # high keys inside prefix + # low keys outside prefix

cannot increase for any such cut. This is a useful global potential; it
does not require balance or a pure reservoir.

However, a particular bag can acquire a stranger relative to its *other*
boundary. A very low key in the later core moves left under min assignment;
it may remain below the earlier bag's native interval. Likewise, a high
outer-interval key can move right. The total outside-parent contamination of
the pair is conserved, but it can concentrate in one child. Therefore
monotone global crossing potential does not imply the existing per-bag,
per-ancestor stranger invariant.

Odd/even adjacent-pair rounds have two matching phases per sweep, but no
convergence bound follows just from this monotonicity. An imbalance can
travel across many bins. Nonadjacent or hierarchical repairs can accelerate
transport, provided the same ancestor/local-error bookkeeping is proved.

## A concrete next proof interface

The joint-core step should expose four quantities, not merely a halver error:

1. Outside residuals `a,b` at the repaired threshold.
2. Count imbalance `Delta` for that threshold and union.
3. Total contamination outside the pair's parent interval, and its allocation
   between outputs.
4. Core sizes and comparator depth, with physical orientation hypotheses.

The exact identity supplies item 1's output from items 1 and 2. Conservation
supplies an aggregate bound for item 3, but distributing it within the old
geometrically decaying invariant is still unresolved.

Before building a sixteen-bin sorter, the useful next research question is
whether a hierarchical scheduler with an **aggregate ancestor-crossing
invariant** can use these monotone pair repairs while permitting temporary
concentration of errors in individual bags. That would be a substantive
scheduler change, rather than a drop-in root repair. Its eventual separator
requirements and stage factor must be rederived.

## Assessment

Paired cores give a real improvement in the correctness interface: balanced
repair needs no independently pure probes and preserves the maximum residual,
rather than summing both sides. This resolves part of the reservoir obstacle.
It does not yet provide cheap dense-core selection, balance at all boundaries,
or preservation of the existing per-bag invariant. Current scalar budgets
do not establish an improvement over the 561-layer complete root repair.
