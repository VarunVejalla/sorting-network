# UB-28 width-32 terminal: Bellman certificate interface

Status: derived proof interface, no continuous certificate yet.

## Network and event

Use Batcher's depth-15 sorter independently on each 32-wire block. For every
dyadic width `h = 64, 128, ..., n/2`, use two alternating-offset matching
passes, with `d_h` independent uniform matchings per pair and offset. Take
`d_h=223` or `27` according to scale parity measured from the top. The depth
is

```text
15 + 2 * sum_h d_h = 250 log2(n) + O(1).
```

After the exact 32-wire sorters, all internal block pairs are ordered. At a
boundary between adjacent blocks with densities `a,b`, an inversion exists
exactly when `a > 0` and `b < 1`. Thus the terminal bad set in density space
is the union of these two strict inequalities, evaluated on integer counts
at width 32.

## Exact local rate ingredients

Let `H(t)=-t log(t)-(1-t)log(1-t)`, with continuous endpoint values. In a
matching round on two width-`h` blocks, input densities `a,b` have conserved
total `c=a+b`. If the output left density is `x` (the overlap density of the
two one-sets), the one-round log-probability per wire is

```text
J(a,b,x) = b H(x/b) + (1-b) H((a-x)/(1-b)) - H(a),
```

on the feasible Fréchet interval `max(0,a+b-1) <= x <= min(a,b)`, with
endpoint terms interpreted continuously. For `d` rounds, the pair action is
the supremum of `sum_t J(a_t,b_t,x_(t+1))` over the intermediate overlap
densities; after each round the pair densities become
`(x_(t+1), a_t+b_t-x_(t+1))`. This is a one-dimensional fixed-total optimal
control problem.

When a parent block of width `h` and density `r` is split uniformly into
children of width `h/2` with densities `u,v` (`u+v=2r`), the split log-rate
per parent wire is

```text
S(r,u,v) = (H(u)+H(v)-2H(r))/2.
```

Both `J` and `S` are nonpositive. A one-scale action `q_{s,p}(z,z')` is the
supremum of the sum of these matching and split rates over every internal
profile path connecting source profile `z` to target profile `z'`. Here `s`
is the 223/27 schedule parity and `p` is the support-phase state. In
particular, the two offsets share the intermediate profile; their maxima
cannot be taken independently. The phase audit gives 41 reachable support
states and 91 possible arcs, with at most six density coordinates.

## Interior supersolution

For each phase `p`, schedule parity `s`, and profile `z` on that phase's
support, find a bounded function `U[s,p](z)` such that every feasible
one-scale path satisfies

```text
q[s,p](z,z') + U[1-s,p'](z')/2 <= U[s,p](z).
```

The phase target `p'` is the audited support transition. Applying this
inequality at consecutive widths makes the profile at one scale the actual
source at the next; it does not permit a fresh representative from the same
coarse cell. The factor `1/2` is the ratio of successive block widths.
Consequently, from width `n/8` down through any fixed cutoff, the total
per-input-wire log action is at most

```text
U[s,p](z)/8 + O(2^-K),
```

after `K` interior scales, with bounded `U` controlling the terminal term.

The two top scales need a separate interface. Write `B(a,b)=(H(a)+H(b))/2-
log(2)` for the initial half-block count rate. If `q_top,0` and `q_top,1`
are the first two scale actions and `z_2` is the resulting width-`n/8`
profile, it is sufficient to prove uniformly over top densities and all
phases that

```text
B(a,b) + q_top,0/2 + q_top,1/4 + U[s,p](z_2)/8
    <= -log(2) - epsilon
```

for some `epsilon>0`. The finite exact width-32 terminal predicate and
method-of-types then give an expected number of failing inputs at most
`n * exp(-epsilon*n + o(n))`, which is below one for sufficiently large
powers of two. Zero-one principle and wire restriction yield the claimed
limsup coefficient 250.

## What remains to derive and certify

1. Formalize the finite phase transition table and the all-scale representative
   lemma below; the latter reduces every dyadic scale to finitely many exact
   boundary positions and two interior residues.
2. Compute rigorous interval upper bounds for the fixed-total, `d=223` and
`d=27` matching actions, then compose them with the split action while
retaining the shared intermediate profile.
3. Find a bounded phase/parity potential and certify the supersolution
inequality on the entire continuous profile domains. The existing flat-cell
Bellman fails because it resets within-cell densities between transitions.
4. The grid-16 screen is contradicted by an off-grid modal path ending at
   `(29,28)` for the width-32 boundary event; see
   [`UB28-WIDTH32-TAIL.md`](UB28-WIDTH32-TAIL.md). First prove the path's
   all-scale recurrence or otherwise exclude it. Until then, its apparent
   positive margin is not a credible target for interval certification.
5. Bound the uniform finite-width entropy error and path count by `o(n)`;
then prove the randomized-network existence step and formalize the fixed
sorting tail and depth arithmetic.

The current schedule screen and native transfer results are in
[`UB28-WIDTH32-TAIL.md`](UB28-WIDTH32-TAIL.md). No Lean stage bridge should be
started until items 2–4 yield a certified strict margin.

## All-scale support-phase representative lemma

For an interval support `[l,l+L)` in `B` blocks, the phase is
`(L, l mod 2, min(l,6), min(B-l-L,6))`. One reverse scale first maps the
interval to
`[floor(l/2), floor((l+L-1)/2)+1)` in `B/2` blocks and then closes it under
offsets 1 and 0. Each closure can move either endpoint by at most one block.
Away from the outer boundary, the target interval's length and left parity
depend only on `L` and `l mod 4`; near an outer boundary the exact boundary
distance determines whether a closure is clipped.

All active block counts are powers of two. For `B <= 128`, the representative
enumerator uses every possible left endpoint, so it is exact. For `B >= 256`,
partition placements as follows. If `l < 32`, the left-boundary representatives
include that exact `l`; the opposite gap is at least `256-31-6`, so after
halving and two closures the target right gap is still at least 6. The
symmetric statement holds when `B-l-L < 32`. These two cases cannot overlap.
Otherwise both gaps are at least 32. After halving and two endpoint extensions,
both target gaps remain at least 14, hence both target caps are 6. In this
interior case only `l mod 4` can affect the target phase, and the central
representatives include both residue classes compatible with the source
parity. Therefore the representative set gives exactly the same set of target
phases as all `B-L+1` placements, for every power-of-two `B`.

Combining the exhaustive small cases with this large-scale argument makes the
41-state/91-arc graph an all-scale finite abstraction, provided the audited
finite table is checked in the eventual formalization. The computational audit
now also compares the exact target-phase sets with the representative target
sets for every interval length 1 through 6 at powers `B=2^8,...,2^18`; it
passes. This removes the representative-position extrapolation as an
independent asymptotic gap; it does not address the continuous-profile
Bellman certificate.
