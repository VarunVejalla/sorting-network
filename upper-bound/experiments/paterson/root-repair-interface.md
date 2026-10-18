# Root-repair interface extracted from the existing proof

Status: source-level extraction and informal adapter argument, 2026-10-10.
No new kernel-checked construction is asserted here.

## Context and notation

Use the hypotheses of `allocatedRebuild_preserves` and `childRegisters_pure`:
`k >= 6`, even phase `t`, nonnegative root, an allocated stored placement `pl`,
an injective rank input `w`, and the existing Paterson stranger invariant.
Writing `C = capacity fastParams root t 0`, the split window additionally has
`300000 <= C <= 300000 / .707^2`.

Let `U = upperRegisters pl`, `N = |U|`, and

    B(L,q) = positionalBin U L q,
    I(L,q) = [q * bagSize k L, (q+1) * bagSize k L),
    D_L = |deepErrors pl w L|.

The allocation proves `64 | N`, so bins through level 4 have exact integer
widths. The rebuilt level-2 and level-4 bags are fixed subsets of their bins;
their ancestor bins have levels `L = b.l - (j-1)`.

## Minimal consumer-facing contract

Choose a comparator network on the local `N` inputs as a function of public
placement/parameters only, scatter it onto `U` in increasing register order,
and call its output `v`. Require, uniformly for admissible `w`:

1. **Locality:** `v(i)=w(i)` for every register outside `U`.
2. **Exact half purity:** for `q=0,1` and `i in B(1,q)`,
   `nativeBagIdx k 1 (v(i)).val = q`.
3. **Rebuilt-bag stranger budgets:** for each rebuilt bag `b` at level 2 or 4
   and every `1 <= j <= b.l`, its assigned registers contain at most
   `mu * delta^(j-1) * capacity fastParams root t b.l` strangers of order `j`.
4. **Depth:** the scattered network has depth at most the proposed repair cost `r`.

Items 1 and permutation preservation follow automatically from the scattered
comparator-network representation. Assignment cards, bin containment, child
register coverage, and child allocation are properties of the existing fixed
rebuild and need no new input-dependent routing.

This is the smallest directly useful interface identified in this audit.
It deliberately says nothing about sorting within bins or about cold-storage
order. It retains the existing placement and rebuild, rather than redesigning
them.

## Convenient sufficient bin contract

A stronger, easier-to-compose condition for item 3 is:

    for 1 <= L <= 4 and 0 <= q < 2^L,
    |{i in B(L,q) : v(i) not in I(L,q)}| <= 2 D_L.

Any subset of a bin has no more errors than the whole bin. Ancestor-bin
containment and `root_rebuild_level2_budget` / `root_rebuild_level4_budget`
then give item 3 verbatim. Level zero needs no condition: its rank interval
contains every input. No level-5 or level-6 bin output condition is consumed by
these rebuilt bags. Level six remains important in the *input* deep-error and
root-purity argument.

The current generic `upper_sorted_bin_errors` states a result through level 6;
its stronger range is not needed for this adapter.

## Error-tolerant sufficient contract

Define the existing scalar bound

    T_L = 64 mu delta^(6-L) C A^6 / (1-4 delta^2 A^2).

The proof already has `D_L <= T_L`. Inspection of
`RootRebuildErrors.lean` gives the exact ratios

    2 T_L = (32/35) * level-4 stranger budget,
    2 T_L = (2/315) * level-2 stranger budget

for the corresponding ancestor level and stranger order. Therefore the
uniform relaxed bin contract

    bin errors <= 2 D_L + E_L,
    E_L <= (3/16) T_L,                 2 <= L <= 4,

still gives every level-4 budget, since its budget equals `(35/16) T_L`.
It also gives the level-2 budgets, whose budget equals `315 T_L`.
Retain exact half purity separately at `L=1`; a scalar tolerance there does
not establish purity.

This relaxation is an informal algebraic derivation from kernel-checked
ratios; adapting the Lean rebuild theorem to use it is still required.

## Adapter proof obligations and source map

| Existing theorem / module | Replacement dependency |
|---|---|
| [RootRebuildContainment](../../alternatives/legacy/AKS/Paterson/RootRebuildContainment.lean) | Keep fixed bin/subset containment unchanged. |
| [RootRebuildInvariant](../../alternatives/legacy/AKS/Paterson/RootRebuildInvariant.lean) | Substitute bin budget for `upper_sorted_subset_errors`; use locality for deep bags. |
| [RootChildRegions](../../alternatives/legacy/AKS/Paterson/RootChildRegions.lean) | Substitute exact half purity; retain existing deep-half purity proof. |
| [ChildInvariant](../../alternatives/legacy/AKS/Paterson/ChildInvariant.lean) | Consume rebuilt invariant and child purity via abstract adapter. |
| [PatersonForestRanks](../../alternatives/legacy/AKS/Separator/PatersonForestRanks.lean) | Replace concrete root network; preserve child-rank reduction and global input-independent final arrangement. |
| [PatersonForestDepth](../../alternatives/legacy/AKS/Separator/PatersonForestDepth.lean) | Substitute `r` for 561 on split branches. Terminal sorting remains separate. |

The forest-rank induction does not require the root operation to have an
input-independent *internal* output order. Its child sorters establish the
final rank arrangement. The replacement still has to be integrated through
that induction, not just through the local stranger proof.
