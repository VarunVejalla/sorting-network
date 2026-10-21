# UB-28 joint-pattern state: research sketch

Status: independently reviewed state hypothesis; no probability bound is claimed.

The width-2 example in `UB28-TOP-HEAVY-SCHEDULE.md` rules out a Markov state
consisting only of block counts. The schedule may still admit a bounded-width
joint state for a fixed terminal inversion: its backward dependency cone has
only finitely many blocks at each dyadic scale, even though each block's width
grows.

For a tuple of `k` supported blocks, write the wire-column type at position `t`
as `v_t in {0,1}^k`, and let `H_v` count positions of each type. The candidate
state is the histogram `H=(H_v)`, together with the exact ordered block labels
and finite pairing/edge phase. A fresh uniform cross-matching is equivariant
under a common permutation of all coordinate slots: conjugating each matching
permutation by the common relabeling preserves its uniform law. Thus equal
histograms in the same labeled geometry have the same next-histogram law.
Conditional on `H`, common exchangeability makes the type sequence uniform over
its orbit.

At a physical half split, retain the **joint allocation** of every row type to
the first and second halves. Conditional on parent histogram `H`, these
allocations have the multivariate-hypergeometric law; the pair of child
histograms remains coupled through the shared allocation. This distinguishes
the width-2 counterexample: aligned singleton blocks have histogram `{00,11}`,
while independent singleton blocks have `{01,10}`. Replacing either by two
separate block counts loses the relevant information.

This state is plausible for a fixed, phase-tagged support geometry. Erasing
block labels/offset phase is unsafe. Support updates must project only whole
block rows and must never discard a row that can later re-enter the cone. The
safe construction is to compute the complete backward cone first, use nested
row sets as the computation runs forward, and retain the joint histogram on
the current full cone. A whole-row projection maps its histogram by summing
over omitted coordinates and preserves diagonal exchangeability. The cone
must be proved uniformly bounded, including boundary data and any
paired-witness labels.

The support-size bound has an all-scale closure proof. At the exact tail, each
bad output edge depends on a contiguous interval of at most six width-4 block
counts. For any contiguous support interval of `s` blocks, closing backward
through the two matching offsets can extend it by at most two blocks at either
end, so its size is at most `s+4`; the subsequent split projection
`j -> floor(j/2)` maps an interval of length `q` to one of length at most
`ceil(q/2)`. Hence `s_next <= ceil((s+4)/2)`, which sends `s<=6` to
`s_next<=5` and in particular preserves `s<=6`. Boundary clipping only
shortens intervals. Thus every scale in the fixed-edge cone has at most six
labeled block rows. The finite script `ub28-backward-window-support.py`
checks endpoint and boundary bookkeeping for powers through 4096; the interval
argument gives the uniform bound.

## Orbit lemma to formalize

Let `S_h` act on a `k × h` Boolean matrix by simultaneously permuting its
columns. Two matrices lie in the same orbit exactly when they have the same
row-type histogram `H`. Suppose a stochastic layer kernel `K` is equivariant:
`K(σ·x, σ·A) = K(x,A)` for every `σ ∈ S_h`. Since each histogram orbit `O'` is
itself invariant, `K(x,O')` is constant on each input orbit. Therefore the
quotient transition on histograms is strongly lumpable. A uniform matching
layer has this equivariance: conjugating each independent uniform matching
permutation by `σ` preserves its distribution, and comparator orientation is
unchanged. This handles any fixed labeled set of disjoint block pairs; the
pair labels and offset phase stay in the state description.

For the split, conditional on input histogram `H`, the parent matrix is
uniform on its orbit. If `x_v` copies of type `v` fall in the first half, then
`Pr[(x_v)_v] = ∏_v binom(H_v,x_v) / binom(h,h/2)` subject to
`sum_v x_v=h/2`; the second-half allocation is `H_v-x_v`. Conditional on both
allocations, the two half-sequences are independently uniform arrangements.
To form a single next-scale histogram on all labeled child blocks, randomly
align these two type multisets at their local wire coordinates and aggregate
the resulting concatenated child types. This retains the correlation lost by
separate per-block hypergeometric splits. The next-scale law is again invariant
under common slot permutations, so it is histogram-lumpable.

For one random matching of labeled blocks `i,j`, fix any representative
row-type word `u_1,...,u_h` of histogram `H` and let `π` be uniform in `S_h`.
The output row type at slot `t` replaces its `i,j` bits with
`(min(u_t[i],u_{π(t)}[j]), max(u_{π^{-1}(t)}[i],u_t[j]))`; every other bit
comes from `u_t`. Thus the exact transition is

```text
K(H,H') = (1/h!) * #{π : histogram(F(u_{π^-1(t)},u_t,u_{π(t)}) over t) = H'}.
```

Conjugation makes this independent of the chosen representative. The triple
dependence explains why a pairwise-overlap approximation is insufficient. A
direct asymptotic route is to count empirical triple types along permutation
cycles, then optimize their entropy subject to the input and output
histograms. Short cycles and finite-width errors must be included in a
certified envelope.

These arguments prove the abstract orbit steps, conditional on the support
geometry being fixed and all random pairings in the local cone being fresh and
uniform. The complete backward cone has to be computed first: an omitted row
cannot be reconstructed from the histogram if it is later added back.

The fixed exact tail has a count-only endpoint predicate. In a width-`h`
left/right block pair, use the `h` cyclic matchings pairing left slot `i` with
right slot `i+s mod h`, for `s=0,...,h-1`. Every cross pair is compared once.
Left bits only decrease and right bits only increase. If a final left bit were
`1` and a final right bit `0`, those same bits had values `1,0` when their
unique comparator ran, contradicting that comparator's output. Thus there is
no such inversion at the end. Conservation of the total `T` then forces the
left/right counts to be `max(T-h,0)` and `min(T,h)`, for arbitrary input
patterns. Applying this at widths 4 and 2 fixes the width-2 counts from the
incoming width-4 counts.

For completeness, let `c_j in {0,1,2}` be the count in width-2 block `j` after
the width-2 split. The final even width-1 pass sorts each block to
`00,01,11`. The odd pass compares the last bit of block `j` with the first
bit of block `j+1`. Its output first bit in block `j` is
`[j=0] ? [c_0>=1] : ([c_{j-1}>=1] or [c_j=2])`; its output second bit is
`[j=m-1] ? [c_j=2] : ([c_j>=1] and [c_{j+1}=2])`. Each adjacent pair is sorted
iff the first expression is at most the second. This is exactly the predicate
in `ub28-terminal-count-gate.py` (including its two endpoint cases). Thus the
entire fixed tail's bad-edge event is a function of the incoming width-4
counts; it needs no marked-slot state. The companion finite checker exhausts
all width-4 count profiles through length 6 against literal bit-level
execution. The proof above, rather than that finite check, establishes the
arbitrary-length claim.

If closure holds, the proof program would be:

1. Prove a conditional exchangeability invariant for each cone phase, including
   the exact tail and the deterministic half split.
2. Prove strong lumpability for the exact histogram transition under every
   phase-tagged random matching pass; count the needed random-permutation
   contingency/cycle types and carry the joint split allocation. A simple
   pairwise contingency table may not encode the permutation-cycle effects.
3. Bound the large-`h` transition by a certified method-of-types/entropy
   operator, preserving positivity and uniform finite-width errors.
4. Optimize the rate over every edge phase and boundary class for a schedule
   whose depth coefficient is below 300; require the bad-edge exponent to
   exceed `ln 2` with explicit slack.
5. Sum the subexponential trajectory and edge factors, then use the first
   moment and wire restriction to obtain the all-`n` limsup bound.

The exact small-width check passes for `(h,k)=(2,6),(4,3),(4,4)`: it enumerates
every input pattern, checks both adjacent pair phases under every uniform
matching, and compares the joint half-split law against the
multivariate-hypergeometric allocation. It also checks the complete two-offset
composition at `(h,k)=(2,4)`. This supports the orbit argument but is not a
proof for arbitrary width or the all-scale support cone. For a matching
permutation `π`,
the new two comparator bits at slot `t` depend on the old row types at
`π⁻¹(t), t, π(t)`. Thus a large-width rate proof will likely need entropy
bounds on cyclic triple-type frequencies (or a looser certified envelope),
not just pairwise overlap counts. If closure fails, enrich the state or park
the route. Even if it passes, the rate
gate remains open: no numerical evidence yet shows that the worst joint-pattern
rate clears `ln 2` for a schedule below coefficient 300. No Lean work should
start before arbitrary-width closure, a rate screen, and independent review.
