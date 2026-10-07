# Can a good sorter be amplified without losing its coefficient?

Investigation: 2026-10-06. All logarithms are base two. No Lean
formalization or proof of existence of the limit is claimed here.

**Follow-up, 2026-10-07:** [Repair interfaces and the staged-composition barrier](sorter-repair-barrier.md)
now gives checked extraction/dependency lemmas and a stronger mathematical
obstruction to local-module stages with small binary repairs. Its status map
supersedes this note's earlier speculation about universally cheap repair.

## The sufficient theorem, including its quantifiers

Let L = liminf D(n)/log n. It would suffice to prove, for arbitrarily
large near-optimal base sizes m, an amplification bound

    D(m^r) <= r (D(m) + e(m)) + B(m)   for every positive integer r,
    e(m)/log m -> 0.

B(m) may be enormous, but must not depend on r. Fix m first and send
r to infinity. Monotonicity and padding, with m^r <= N < m^(r+1), give

    limsup D(N)/log N <= (D(m) + e(m))/log m.

Then take near-liminf base sizes m to infinity. This proves equality
of liminf and limsup. This argument is elementary and unaudited, not a
kernel-checked result. A bound only for bounded r as a function of m is
insufficient without an additional coverage argument for all large N.

## Opaque composition has a genuine obstruction

Dobrokhotova-Maikova, Kozachinskiy, and Podolskii prove that a depth h
network of k-input sorting gates on N inputs satisfies

    k >= (N/2)^(1/ceil(h/2)).

For k=m and N=m^r this forces h >= 2r-O(1). Substituting a binary
depth-d sorter for each gate, layer by layer, therefore has scheduled
depth at least (2r-O(1))d. This disproves coefficient preservation by
this particular opaque substitution strategy. It does not lower-bound
the optimal binary depth of the resulting graph after internal-layer
rescheduling, or constructions that reuse internal partial results.

Source: [Constant-Depth Sorting Networks, ITCS 2023](https://drops.dagstuhl.de/storage/00lipics/lipics-vol251-itcs2023/LIPIcs.ITCS.2023.43/LIPIcs.ITCS.2023.43.pdf).

## A universal interface exists, but its cost is too large

An arbitrary sorter can operate on sorted packets: replace each
comparator by merging two sorted packets and splitting the result into
its lower and upper halves. The packet version sorts the concatenated
data. This is the standard block comparator principle; see CLRS,
exercise 28.5-3.

However, an exact compare-split of packets of length b requires
Omega(log b) binary depth. The middle output depends on a linear number
of input positions even under the sorted-packet promise, whereas a
depth t output has at most 2^t input ancestors. Batcher merging supplies
an O(log b) implementation. The direct simulation of a depth-d base
sorter costs O(d log b), in addition to preparing the packets.

Using b=m^(r-1) at recursive scale r and finishing every packet operation
before proceeding leads to a depth accounting of order d log(m) r^2.
This describes the direct implementation, not a lower bound against all
possible pipelined packet implementations. Componentwise min/max of two
packets is cheaper, but fails: if every packet has the same half-zero,
half-one pattern, componentwise comparisons change nothing.

Reference: [CLRS sorting-networks chapter, exercise 28.5-3](https://bobson.ludost.net/books/algo/book6/chap28.htm).

## A concrete partial interface and its overhead

An s-sorted Boolean array has only one possibly unsorted interval of
length s. The interval is input dependent. Lemma 18 of the paper below
merges p such arrays of length n in one layer of gates of arity at most
pt, obtaining uncertainty at most

    s' <= p s + 2np/t.

Putting q=s/n gives q' <= q+2/t. Choose pt<=m and substitute the good
m-sorter for each gate: the binary stage costs at most d=D(m), grows
array length by p, and increases the certified relative uncertainty by
2/t. With t approximately m^delta and p approximately m^(1-delta), its
apparent depth coefficient is d/((1-delta)log m), close to d/log m when
delta is small. But after r stages the bound is q_r <= q_0+2r/t.

For fixed m this invariant becomes useless as r tends to infinity.
That is a failure of the guarantee, not a proof that every output of
this construction has that much error. Increasing t with r eventually
violates pt<=m or reduces the expansion factor. Periodic repair is the
missing cost, rather than a free consequence of the interface.

Even if uncertainty were bounded by a small fixed fraction q of N,
sorting a remaining interval of length qN by a fresh O(log N) sorter
does not have vanishing relative depth: log(qN)/log N tends to 1 for
fixed q>0. More generally, uncertainty N^alpha gives a generic repair
cost proportional to alpha log N. Subpolynomial uncertainty is needed
to make this particular final repair negligible. The interval location
is also unknown; handling all possible positions requires a fixed
network construction, not an adaptive selection of the actual interval.

Source: [Towards Simpler Sorting Networks and Monotone Circuits for Majority, Definition 16 and Lemma 18](https://kozmath.github.io/papers/upper_bounds.pdf).
The recurrence and overhead analysis here are our deductions from the
lemma. The paper's sorting upper bound is quadratic in log_k N, not a
coefficient-preserving amplification theorem.

## Reusing internal layers: matching lifts

Replace each base wire i by b copies, ordered by i then copy index.
For each base comparator (i,j), match these two fibers by a permutation
and compare every matched pair, with min sent to fiber i. Each base
layer remains one binary layer. Thus the lift has mb inputs and exactly
the base depth. Different gates can use different matchings.

There is a weak guarantee for **every** lift. An output one in base
fiber i (zero-based) needs ones in at least m-i distinct input fibers.
Indeed, let T be the fibers containing any input one. Replacing each
fiber in T by all ones dominates the original input. On this uniform
input, any lift is just b copies of the original sorter. Its output in
fiber i is one only if |T| >= m-i. The dual statement holds for zeros.
In particular, for even m, at most m/2 input ones cannot leak into the
left half, and at most m/2 input zeros cannot leak into the right half.
This proof uses monotonicity and is derived here; it is not formalized.
It is an absolute rare-rank guarantee, not a uniform small-error halver.

The executable probe exhausts every Boolean input for each selected
lift, measuring the worst ratio of misplaced ones or zeros to their
total count, for each count 1 through mb/2. It checks the original
Batcher odd-even sorters on 4 and 8 inputs too.

| Base m | Copies b | Depth | Identity lift error | Best sampled error |
| --- | --- | --- | --- | --- |
| 4 | 2 | 3 | 1/2 | 1/4 |
| 4 | 4 | 3 | 1/2 | 3/8 |
| 8 | 2 | 6 | 1/2 | 1/4 |

Each row samples seeds 0 through 63, plus the identity lift. These are
exact exhaustive-input results for those networks, not a search over
all lifts and not an asymptotic theorem. Reproduce with
`python scripts/sorter_lift_probe.py` (NumPy required). Best seeds are
4, 16, and 0 respectively; the script prints explicit worst inputs.

Independent-population mixing is an additional caution. Starting all
fiber densities at 1/2 and replacing each comparison by the mean-field
update (x,y) -> (xy,x+y-xy), the left-half leakage ratios for Batcher
base sizes 64, 256, 1024, and 2048 are respectively 0.0201883,
0.0118310, 0.0113690, and 0.0113689. This numerical model assumes
independence and cannot certify any adversarial-input guarantee or
prove a positive limiting error. It gives no evidence that this family
automatically becomes an arbitrarily accurate separator.

## Conclusion and a useful next theorem

We have not found a simple coefficient-preserving construction. Exact
opaque composition is obstructed; packet lifting is expensive; the
published partial interface loses control across indefinitely many
scales. Internal-layer lifting offers some separation at unchanged
depth, but neither uniform asymptotic error nor cheap composition has
been established. A small halver error alone does not imply a scheduler
with coefficient loss tending to zero.

A more informative next target is a **repairable** interface, with both
an error invariant and an explicit correction schedule. One possible
form is: grow scale by m^(1-o(1)) using the base layers, while corrections
cost o(log m) amortized per scale, uniformly in the number of scales.
Errors should be confined to known local buffers, or retain enough
routing information that corrections do not restart global sorting.
If the buffers themselves require fresh sorting, their size must have
logarithm o(log m) to meet that budget. This is a target, not an asserted
necessary condition for every conceivable amplification method.

Before investing in a full construction, prove such a repair lemma for
two consecutive scales, or prove that a specified interface cannot do
it. The main missing result is cheap repair, not merely extracting some
partial sorting behavior from a good sorter.
