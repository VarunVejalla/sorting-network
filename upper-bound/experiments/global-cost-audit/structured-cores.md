# Structured cores: merge reuse and the global depth test

Status, 2026-10-10: mathematical cost audit of a possible interface. The
run-merge primitive below follows from standard bitonic merge, but its adapter
to the Paterson invariants and the proposed closure theorem are not proved.
This note establishes no new sorting bound.

## Conclusion

Keeping a core as a sorted run can replace a repeated exact sort of two cores
by a merge, but it does not by itself give a linear-logarithmic sorting
construction. There are two independent gaps:

1. the existing supported-halver cascade produces an arbitrary set of core
   values, not a sorted run, so its first run construction still costs
   `Theta((log f)^2)` with the repository's Batcher sorter; and
2. after a core is merged with one neighbour, the population of its block has
   changed. Sortedness survives, but the former all-supported-rank extreme-core
   certificate does not automatically survive for a later neighbour.

The second point is the real correctness question for reuse. The first is
already enough to reject charging a dense run initialization at every
unbounded scale.

## A constructive interface that is actually available

Let two fixed cores have equal size `f`, and suppose each is sorted. Reverse
the wire order of the right run (a relabelling, not a comparator layer), then
apply a bitonic merge to the union. For power-of-two padded size `2f`, the
existing bitonic merge has depth at most `ceil(log_2(2f))`. Assign the first
`f` sorted outputs to the left core and the last `f` to the right core. Both
output cores remain sorted, so this operation can be repeated without another
sort.

At every threshold, if `a` is the number of high keys outside the left core,
`b` the number of low keys outside the right core, and the pair contains
`f`-quota imbalance `Delta` as in the paired-core audit, the resulting errors
are still exactly

    left high  = max(a, b - Delta),
    right low  = max(b, a + Delta).

Thus sorted-run merge realizes the already derived fixed-quota identity at
merge depth rather than sort depth. Unequal and non-power-of-two cores require
a restriction/padding lemma with the requested quota; that adapter is not
presently proved.

This interface deliberately assumes sorted runs. It makes no claim that an
unsorted supported core can be selected, split, or sorted cheaply.

## Cost against the current four-block proposal

For the largest audited root blocks, a one-stage supported concentration has
depth `13` and leaves a half-block core. The previous arbitrary-core joint sort
was charged `435`, giving pair depth `448` and three-phase epoch depth `1344`.
If the two half cores were already sorted runs, their joint merge would cost
at most about `29` layers, so a refreshed pair would cost about `42` and an
epoch about `126`. If concentration could be omitted because a reuse invariant
closed, the corresponding numbers would be about `29` and `87`.

These are conditional local budgets. They do not define a complete root
repair: the conservative epoch contraction is only `5/8`, support must hold at
all ranks up to `.0398m`, all sixteen bins and imbalance terms must be covered,
and the final residual must be eliminated exactly.

Repeated contraction also fails the asymptotic test for dense cores. Reducing
`Theta(n)` error to below one takes

    ceil(log_(8/5) n) = about 1.475 log_2 n

epochs. If a merge at that scale costs `Theta(log n)`, the total is
`Theta((log n)^2)`. Shrinking the core geometrically with the error does not
fix this: summing `log f_t` over a linear number of contraction epochs is still
quadratic in `log n`. A linear-log bound therefore needs constant-depth
repairs, a constant number of repairs at each bounded-size window, a pipeline
that proves overlapping merge levels execute in parallel, or a stronger
contraction whose number of sequential dense merges is bounded. None is
currently constructed.

## What reuse must prove

Sortedness is closed by merge; extreme capture is not. A reusable block needs
separate interfaces for its low and high boundaries, because a core used to
send large values right is generally not the core needed to send small values
left. The four-block schedule also uses nonadjacent pairs. Sharing wires among
these roles creates sequential conflicts, while disjoint left/right cores
consume additional capacity.

The required theorem cannot merely say that a run contains most of one
specified cohort. It must quantify over every rank `j <= K` and must be stable
after fixed-quota merges. A useful candidate statement is:

> **Persistent two-sided run closure.** Each block owns disjoint sorted low and
> high runs and an exterior. For every `j <= K`, at most `epsilon*j` of its
> smallest (respectively largest) `j` keys lie outside the corresponding run.
> Under one specified fixed-quota run merge, give explicit new `K`, `epsilon`,
> exterior-error, and imbalance bounds for both participating blocks, and show
> that the untouched opposite runs retain their contracts.

The statement should first be attempted for one adjacent balanced pair. If it
is false, a count-state counterexample will stop the reuse route cheaply. If it
is true, compose exactly the five operations of the four-block epoch and audit
wire disjointness phase by phase. Concentration should be charged again
whenever this closure theorem does not apply.

This is stronger and more informative than proving another exact selection
oracle: it identifies whether the structure paid for once can genuinely be
carried through the scheduler.

## Global coefficient barrier

With the completed Paterson comparison scheduler unchanged, the asymptotic
coefficient is

    6.5 * 989 + r + 1 = 6429.5 + r,

where `r` is the complete per-level root repair. Even a free persistent-core
root repair leaves `6429.5`. Replacing the current `561` root cost by the
conditional `126` epoch cost would give `6555.5` before accounting for enough
epochs, sixteen-bin integration, and exact cleanup. It cannot approach `1000`,
let alone `200`.

Consequently a sub-1000 result requires a new interior primitive and global
scheduler whose full per-logarithmic-scale charge is below `1000`. A target of
`200` leaves correspondingly little room for every separator, movement,
repair, and terminal-sort charge. Improving only core sorting is irrelevant to
those targets.

## Recommended next lemma and decision gate

Prove or refute persistent two-sided run closure for one balanced adjacent
pair, including all-rank support, both boundary runs, and the exact exterior
error after the merge. In parallel with its statement, give the comparator
realization and the depth `ceil(log_2(f_L+f_R))` for the fixed quotas actually
used. Do not assume a cheap first creation of the runs.

Only after that lemma closes should the four-block composition be costed. A
viable global proposal must then exhibit one of the asymptotic escape routes
above and replace the `989`-depth interior stage in the complete scheduler.
Absent both items, structured cores are a possible constant improvement to a
bounded root repair, not a route to coefficient `1000` or `200`.
