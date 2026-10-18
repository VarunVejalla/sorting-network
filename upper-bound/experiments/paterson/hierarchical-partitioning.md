# Hierarchical partitioning investigation

Status: informal sufficient construction and error accounting; the cheap
partition primitive remains unconstructed. See the [repair interface](root-repair-interface.md).

## Exact four-level partitioning suffices

Suppose `P(m)` is the depth of an oblivious comparator network that partitions
every distinct-key input of even size `m` into its smallest and largest `m/2`
keys, on fixed left/right output blocks. Ordering inside either block is free.

Apply it once to `U`, then to its two halves in parallel, then its four quarters,
then its eight eighths. Since `64 | |U|`, all these splits are integral. The
result has sixteen blocks equal, as value sets, to the sixteen consecutive
local-rank blocks of `U`. Consequently every bin at levels 1 through 4 has
exactly the same value set that a complete sort of `U` would put there.

The existing prefix-discrepancy proof therefore gives the same bin error
bounds as sorting. At level 1, `D_1=0` gives native-half purity. Ordering within
the sixteen blocks is irrelevant: any rebuilt subset has error count bounded
by its containing bin, and the later children sort their native halves.

The repair depth is bounded by

    r(N) <= P(N) + P(N/2) + P(N/4) + P(N/8).

There are four sequential partition levels, regardless of the number of nodes.
This is a sufficient construction theorem, not an efficient implementation:
if `P` is implemented by full sorting at every node, it offers no improvement.

## Approximate inner partitions: explicit error propagation

Make the first split exact. For a subsequent node, measure its split error as
the number `tau` of keys in the wrong half *relative to the sorted order of
that node's actual input set*. The halves have equal cardinality, so the two
wrong-half counts agree. This must be a uniform network guarantee, not an
input-dependent choice of comparisons.

Let `J(L,q)` be the ideal local-rank block of the original `U`, and let `V(L,q)`
be the actual value set in the corresponding output bin. Put

    d(L,q) = |V(L,q) \ J(L,q)| = |J(L,q) \ V(L,q)|.

The equal-size lower-half and upper-half selection maps are 1-Lipschitz in
this set-replacement distance: replacing `d` keys in a parent set changes
either selected half by at most `d` keys. One proof matches the common keys
in sorted order; the half cutoff shifts by at most the number of replaced
keys, and the added selected keys account for the rest within the same `d`.
Approximate splitting and the triangle inequality thus give

    d(child) <= d(parent) + tau(node).

With uniform split bounds `tau_2,tau_3,tau_4`, this yields

    d(L,q) <= tau_2 + ... + tau_L,       L=2,3,4.

The ideal bin has at most `2 D_L` wrong native-interval keys by the existing
prefix-discrepancy argument. At most `d(L,q)` additional keys can enter its
actual value set. Hence

    actual bin errors <= 2 D_L + sum_{h=2}^L tau_h.

A sufficient condition for the relaxed repair interface is therefore

    sum_{h=2}^L tau_h <= (3/16) T_L,     L=2,3,4,

together with exact first splitting. Errors accumulate along a path;
they are not multiplied by the total number of partition nodes.

This argument still needs a finite-set Lean proof of the selection stability
lemma and of the transfer from ideal bins to native rank intervals.

## Actual available error scale

At the smallest root capacity `C=300000`, exact rational evaluation gives
the following sufficient cumulative error limits per output bin:

| Bin level | `(3/16) T_L`, approximately | Conservative integer cumulative limit |
|---:|---:|---:|
| 2 | 80.177455 | 80 |
| 3 | 4570.114955 | 4570 |
| 4 | 260496.552455 | 260496 |

These limits increase linearly with `C`. Thus the second partition is much
more demanding than the later two. The first is exact. A generic constant
fraction halver is not automatically adequate: certify its absolute escape
count at the actual region sizes, including the smallest root window.
The experiment's arithmetic script reproduces these numbers.

For example, cumulative limits can be allocated as local per-node budgets
`tau_2=80`, `tau_3=4490`, `tau_4=255926`. This is only an error budget; no
networks of these costs and errors are established here.

## What can currently be claimed about cost?

The extracted interface reduces the output task from sorting to sixteen-way
partitioning. It does not prove that exact median partitioning is cheap.
In particular, an epsilon-halver with nonzero possible leakage cannot supply
the exact first split. A further repair or selection argument is required.

A familiar bitonic truncation gives a modest illustrative saving when the
region size is exactly `2^h`: sort its two halves in opposite directions
(depth `h(h-1)/2`), then execute only the first four levels of the final
bitonic merge. The bitonic split property separates the sixteen local-rank
blocks, giving depth `h(h-1)/2 + 4` for `h>=4`. At `h=33` this is 532 rather
than 561. This is an informal special-case construction, not a verified
bound for the actual arbitrary `N` in this scheduler.

Padding arbitrary `N` to a power of two does not fix that issue automatically:
the resulting equal padded blocks need not match the required actual cuts
`q*N/16`. An arbitrary-cut partition construction and its proof are needed.
Even a repair cost of 532 would save only 29 in the global coefficient.

## Recommended next research obligation

The input invariant does give useful structure for the first split. At the
largest root capacity `C=300000/.707^2`, the existing bounds imply:

- Root bag plus cold storage contain fewer than 606938 registers, using
  `root + 32 + ancestorReserve(root)` with
  `ancestorReserve(root)=root/(4 A^2-1)`.
- Each level-2 bag has at most 4727 wrong-native-half keys, from stranger
  order 2; across four bags this is at most 18908.
- Each level-4 bag has at most 32 wrong-native-half keys, from stranger
  order 4; across sixteen bags this is at most 512.

Thus, after treating the root and cold storage as wholly uncertain, fewer
than 626358 upper keys are uncertain or misplaced relative to their assigned
native halves. The individual bag leakage bounds follow from the invariant
and integer rounding; the arithmetic script prints their rational ceilings.
This is a *count* certificate, not a fixed set containing those misplaced
keys. Their wires may be anywhere within their shallow bags.

It suggests a concentration-and-repair design: use oblivious filtering to
concentrate the sparse wrong-half keys from levels 2 and 4 into designated
fringes, combine those fringes with the known root/cold registers, and exactly
partition the resulting repair pool. But the filtering must either extract
every wrong-half key or have a subsequent exact cleanup. A positive residual
fraction is insufficient for the first split. Comparator networks also cannot
branch on a numerical native-half threshold; the extraction must be expressed
using comparisons and uniform order guarantees.

Investigate an exact median partition network for the *admissible root inputs*,
exploiting the pre-existing stranger and storage constraints. Decide whether
those constraints localize all uncertain keys to a fixed small repair region.
That localization must be proved; the current bin discrepancy only bounds
counts and does not identify the uncertain wires.

If the first split can be made cheap, combine it with a high-accuracy second
partition and progressively looser third/fourth partitions using the budgets
above. Track their summed depths before integrating the forest adapter.
This is a concrete candidate route to cheaper root repair. It currently
provides no justified repair cost in the tens, and therefore no path to
coefficient 200 by itself.
