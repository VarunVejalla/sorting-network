# Native reservoir supply and oblivious exchange depth

Status, 2026-10-10: exact rational scalar accounting and informal conditional
exchange lemmas. No Lean network implementation or improved repair bound.
Run `python upper-bound/experiments/paterson/reservoir_budget.py`.

## Allocation supply bound

First consider the simple design protecting all original level-4 registers
and pooling the original level-2 registers, root bag, and cold storage. Let
`C` be root capacity and `K=mu*C*A^4` the per-leaf finest stranger budget.
Symmetry of the original level-4 bag cardinalities and the upper-region
conservation identity make each leaf's pool-slot count

    Q = n2/4 + (rootCard+coldCard)/16.

The existing allocation bounds give

    Q <= (C*A^2+32)/4 + (C+32+C/(4*A^2-1))/16.

Across the root window, this upper bound is approximately `.56304 K`.
At `C=300000` it is 1,711,157.584; at the upper root ceiling it is
3,423,339.013. Integer cardinalities are bounded by the floors.
This is an upper bound on fixed pool slots per leaf, not a lower bound on
native keys actually present in the whole pool. Those counts can differ
because of protected contamination and prefix discrepancy.

## Directional prefix estimates improve the accounting, but not the supply

The earlier estimate `|s| <= 16K` ignored the nested stranger invariant.
For a finest boundary, decompose each side into its maximal dyadic blocks.
If such a block contains `2^h` leaves, a key crossing from it to the other
side is strange to that level-`4-h` ancestor. Each leaf contributes at most
`K*delta^h`. Summing the contributions gives directional bounds:

    s(q) <= rightCross(q),
    -s(q) <= leftCross(q).

For example, at the first finest boundary the left bound is `K`, while
the right bound is

    K + 2 delta K + 4 delta^2 K + 8 delta^3 K.

If protected native halves are additionally exact, the whole-half term
vanishes. The script uses that optimistic exact-half condition and retains
the original finer ancestor bounds. **Preservation of those finer bounds
by a proposed half-repair is an additional assumption**, not yet proved.
Removing fixed cores can only reduce an original leaf's ancestor-stranger
count, but transfers/layout can invalidate its original ownership label.

For a sorted pool, a guaranteed native window for leaf `q` has size at least

    max(0, Q_q - D_lo - leftCross(q) - D_hi - rightCross(q+1)).

The endpoints and exact half boundary have zero `D`; other finest cuts use
the existing scalar bound `T_4=(16/35)K`. Even replacing `Q_q` by its optimistic
allocation upper bound makes the expression nonpositive for every leaf.
Thus this directional interval method certifies **zero guaranteed native
probe wires** in every original leaf reservoir. It does not prove that no
native pool keys exist, or that a sharper correlation argument is impossible.

Extracted cores add pool slots and change the discrepancy bounds. This
calculation does not rule out the previous larger-core designs; their
core-specific slot counts and prefix correlations must be recomputed.

## A separate native-resource requirement

Under the conservative target from the signed-prefix audit, even perfect
boundary balance leaves only `(3/35)K` residual local errors after charging
deep errors. Starting from a saturated local budget `K` requires replacing
at least `(32/35)K` wrong keys by native keys, if purification is performed
solely by exchanges with a fixed reservoir.

Each net reduction of one wrong protected key consumes one native reservoir
key; internal protected comparisons cannot change that total. Therefore an
isolated reservoir of size at most `.56304K` cannot guarantee the required
`.914286K` replacements in this saturated case, even if all its keys start
native. This is a resource obstruction for **this isolated exchange model**.
It is not an impossibility theorem for global exchanges, recirculation through
other bins, enlarged cores, or proofs exploiting unsaturated/correlated errors.

## Conditional sparse-exchange lemma

There is a useful oblivious graph criterion when a native reservoir is
available. Treat one error direction at a time:

- Low strangers: comparisons retain the maximum at each protected wire and
  the minimum at its reservoir neighbor.
- High strangers: comparisons retain the minimum at the protected wire and
  the maximum at its reservoir neighbor.

The required endpoint order must be realizable in the current comparator
model. For the following argument assume it is, and initially every probe is
native to the protected interval. Let `K` bound the initial wrong-key count.
Process every edge of a fixed bipartite protected/probe graph, grouped into
disjoint matchings. For the low-stranger pass:

1. A protected wire can cease being low, but cannot become low again under
   maximum-retaining comparisons.
2. A probe can become low, but cannot cease being low under minimum-retaining
   comparisons. Probe corruption is monotone.
3. If `S` is a set of surviving low protected wires, every neighbor in `N(S)`
   is a low probe at the end; otherwise their comparison would have repaired
   its protected endpoint.
4. Conservation therefore implies `|N(S)| + |S| <= K`.

The sharper sufficient expansion criterion is consequently

    |N(S)| + |S| > K whenever |S| > epsilon*K.

It forces at most `floor(epsilon*K)` surviving strangers. The high-stranger
case is symmetric. This corrects the looser sufficient condition
`|N(S)|>K`: the surviving protected keys must also be counted.

Opposite-direction passes need separate bookkeeping. A pool key contaminated
by a low-stranger pass cannot automatically serve as a native probe in a
high-stranger pass. Pure probe supply and interval error budgets must be
re-established or separate reservoirs reserved.

## Depth and graph cost

Every matching costs one layer. A safe graph schedule uses no more than
`degreeProtected + degreeProbe - 1` colors by greedy edge coloring; a sharper
bipartite matching decomposition could reduce this to the maximum degree,
but its formal implementation is additional work. Neither estimate supplies
an expander with the needed neighborhood guarantee by itself.

For a direct-exchange scheme in which each of `M` protected wires must meet
a probe at least once and no protected/internal concentration is used,
each layer touches at most `Q` protected wires. Thus depth is at least
`ceil(M/Q)`. With full-capacity `M=C*A^4` and the allocation upper bound above,
this illustrative requirement is **90 layers just for coverage**.
It is not a lower bound for arbitrary concentration networks, and actual
partial bags may have fewer wires. Expansion for multi-key adversaries and
two directions requires more than mere coverage.

This direct model cannot currently fit the 117-layer suffix margin: native
supply is uncertified and insufficient in its isolated saturated form, and
even coverage at full capacity already uses most of the margin. No concrete
low-depth graph/correctness proof closes the gap.

## Conclusion and next meaningful direction

The original per-bin reservoir is not an adequate certified resource for this
repair interface. Continuing with an expander search alone would bypass the
more basic supply and ownership obligations.

Two substantive alternatives remain:

1. **Global circulation with enlarged cores:** transfer contamination between
   bins while preserving signed prefixes, and prove a joint native-resource
   theorem rather than treating each reservoir independently. Keep explicit
   core-size and comparator-layout costs.
2. **A different rebuild invariant:** reserve enough local slack that existing
   protected contamination and pool spillover can coexist. Recheck the interior
   inequalities and global shrink factor; extra slack is not free.

The exchange graph lemma is a reusable modular result to formalize if supply
can be established. Current evidence favors resolving one of those structural
alternatives before trying to certify a particular sparse-exchange graph.
