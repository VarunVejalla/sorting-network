# Joint bin-preserving pool allocation

Status (2026-10-10): informal set-allocation theorem, an exact spillover
example, and conservative scalar cost accounting. No new root-repair network
or improved sorting bound is proved.

## Allocation problem

Write `N=|U|`, and first work with sixteen equal destination bins of width
`N/16`. Their coarser unions supply levels 1 through 4. Fix a set `P_q` of
protected wires assigned to each finest bin, with fixed cardinality `p_q`.
All unprotected upper wires form the common pool `R`.

To preserve the current rebuild, place protected wires only in the level-4
segment of their destination bin; require `p_q <= n4`, where `n4` is the
existing level-4 allocation size. Include all original level-2 bags and the
root/cold wires in the pool. Each bin then has `N/16-p_q` pool slots.
Sort the pool and allocate consecutive runs to those slots, in bin order.
The level-2 segments and cold slots are filled by this same allocation.

These are assignments of value sets to fixed slots. Realizing them by the
project's comparator networks is a separate obligation, discussed below.

## Exact signed-prefix formula

At a level `L`, boundary `q` has native threshold `theta=q*bagSize k L`
and upper positional prefix size `a=q*N/2^L`. Define:

    g(q) = number of all U keys below theta - a,
    s(q) = number of protected keys below theta
             - number of protected slots assigned before boundary q.

The existing upper-prefix discrepancy gives `|g(q)| <= D_L`, where
`D_L=|deepErrors pl w L|`. Since both protected slot counts and pool slot
counts are fixed, the pool's actual prefix count minus its allocated prefix
length is exactly

    pool discrepancy(q) = g(q) - s(q).

For output bin `q`, let `b_q` be the number of its protected keys outside its
native interval. Sorted-pool allocation implies

    bin errors <= b_q + (g(q)-s(q))_+ + (s(q+1)-g(q+1))_+
               <= b_q + 2 D_L + (-s(q))_+ + (s(q+1))_+.

Here `x_+=max(x,0)`. The first term counts protected errors. The other two
bound low keys spilling past the lower allocated pool cutoff and high keys
appearing before the upper cutoff. Truncation to the actual allocated run can
only reduce these counts.

This gives a precise sufficient condition for a desired whole-bin budget `B`:

    b_q + (-s(q))_+ + (s(q+1))_+ <= B - 2 D_L.

For a rebuilt bag, apply the same argument to its relevant ancestor bin or
derive a sharper version for that bag's actual subset. The current sufficient
level-4 budget has only `(3/16) T_L` spare above `2 T_L`, whereas a retained
original bag may already saturate its entire stranger budget.

## Why half concentration is insufficient

The preceding first-split concentration ensures `s=0` at the half boundary
and native-half purity of protected keys. It does not bound the intermediate
quarter/eighth/sixteenth signed discrepancies tightly enough.

`joint_pool_allocation.py` computes a simple counterexample to the proposed
implication from per-protected-bin errors to the same final bin budget:

- Use ranks 0 through 23, eight bins of width three, one protected slot per
  bin, and two pool slots per bin.
- Protected keys by assigned bin are `6,7,8,9,12,15,18,21`.
- Each protected bin has at most one wrong native-bin key. Every protected
  key belongs to its correct native half.
- Sort all remaining keys and distribute two to each bin.
- Bin 2 receives `[8,4,5]`, hence two wrong keys although its protected key
  is correct. Bin 1 also has two wrong keys.
- Half purity is retained throughout; global prefix discrepancy `g` is zero.

This example isolates the signed-prefix spillover mechanism. It is not a
counterexample to the existing Paterson invariant or an impossibility theorem
for every redesigned allocation: it uses a simplified eight-bin model.
It does show that the previously available output properties cannot by
themselves prove the joint allocation contract.

## A sufficient strengthened construction

Protect only keys proven to be native to their original level-4 bag, assigning
them to that bag's destination bin. Put all non-native keys, all original
level-2 keys, and root/cold storage in the pool.

Then, at every boundary through level 4, protected prefix counts exactly equal
their assigned prefix counts: `s(q)=0`; protected bin errors are zero as well.
Sorted-pool allocation therefore gives

    bin errors <= 2 D_L,

which is precisely the old sufficient root-rebuild contract. Since `D_1=0`,
the halves are exact. Protecting subsets of original level-4 bags respects
`p_q <= n4` and the fixed allocation capacities.

This supplies a clear **set-level** sufficient construction. It needs exact
extraction of both tails outside each native level-4 interval. The low tail
and high tail are extreme cohorts, so supported concentration can apply.
Run one direction first, protect its extracted core in the pool, then run
the other direction only on the remaining block; no wrong key of the first
direction can escape back out. The second direction's budget remains valid.
The two directions cost sequential depth in this simple implementation.

## Cost of that stronger purity baseline

Native-half contaminants in a level-4 bag had budget only **32** at the
largest root window. All non-native level-4 keys instead have first-stranger
budget

    floor(mu*C*A^4) = 6,080,089.

That is a fundamentally larger extraction task, approximately .0199 of the
bag capacity. Applying the existing uniform sparse-concentration envelope at
error 1/4, stopping density 1/10 gives:

| Quantity | Conservative bound |
|---|---:|
| One-sided fixed core per level-4 bag | 168,917,608 |
| One-sided depth | 180 |
| Sequential two-tail core, capped at bag size | 305,532,147 |
| Total pool including all level-2 and root/cold wires | 4,943,287,776 |
| Bitonic full pool sort | 561 layers |

The conservative core envelope retains the whole bag, so it certifies **no
savings**. Concentration plus pool sorting already totals 921 layers before
any layout adapter. Adding a hypothetical four-layer layout gives 925; the
script prints that number only as scalar accounting, not a proved layout or
network bound. A more specialized simultaneous two-tail concentrator might
improve the envelope; the current bound does not prove that no such scheme works.

## Layout caveat for approximate finer bins

The one-layer known-half matching remains sound because half labels are exact.
It cannot simply be repeated three more times based on nominal finer-bin labels.
When `D_L>0`, pool keys allocated to a bin can have the wrong native label.
Consequently a matching designed from those nominal labels need not perform
the intended fixed permutation on real keys.

Even the exact-protected-complement construction above needs a comparator
layout lemma that realizes or safely approximates the set allocation and
preserves its prefix-error estimates. Arbitrary reordering of output wires
is not free under the present network model. Sorting the pool directly on
carefully chosen ordered destination slots may handle the pool's order, but
protected-wire transport still needs explicit construction and error accounting.

## What is worth pursuing now?

The first-split-only bound does not currently extend to a cheap complete joint
repair. Exact finest-bin extraction solves the correctness accounting but
loses the sparse-cost advantage. Leaving contaminated protected keys requires
the explicit signed-prefix inequalities above, which the existing counts do
not automatically supply.

A more focused research target is **balanced signed-prefix control**, rather
than complete purity: concentrate or exchange keys so every protected boundary
has a small net discrepancy, while retaining enough per-bag budget for pool
spillover. This can be weaker than extracting all ~6 million non-native keys
per bag, but it requires a new oblivious balancing argument and a compatible
layout lemma. Another possibility is a rebuilt allocation/invariant with
enough slack to absorb that spillover; its larger error constants must then
be traced through the global shrink factor.

For now, keep the production 561-layer root sorter. The useful result of this
audit is the signed-prefix transfer formula and the identification of the
stronger condition needed to make joint allocation work—not a cheaper repair.
