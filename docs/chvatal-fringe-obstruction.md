# One-round fringe obstruction and the revised route

Research result, 2026-10-10. The elementary argument below was independently
reviewed by two agents, but is not Lean-checked. It supersedes the proposed
one-round small-fringe milestone in [the earlier analysis](chvatal-smaller-fringe.md).

Follow-up: [two-round small ranks](chvatal-two-round-small-ranks.md) gives a
conditional zero-escape lemma and a sharper two-round adversary.

## Exact witness reduction

Let a sorted binary input have column heights `h_u`, total mass `j`, and final
heights `z_v` after a fixed row scramble and column sort. Define
`S = {v : z_v > f}` and escaped mass `E = sum_v (z_v-f)_+`.

Retain every input mark whose scramble image is in S, then take the downward
closure in each input column. The new heights satisfy `h'_u <= h_u`. Every
original hit into S survives; removing input marks cannot add hits. Therefore
each `z'_v = z_v` for v in S, no other column overflows, and `E'=E`, while
`j'<=j`. A violation `E >= epsilon*j` remains a violation after this reduction,
and the supported-rank upper bound remains satisfied.

This is a valid modular extraction lemma. It does not make the target existence
claim true: the reduced witness family contains the adversary below.

## Stronger adversary

Assume f is positive and `m >= 2*f`. Fix any row scramble and a target output
column. In each of the bottom `2*f` rows, select the input cell mapped into that
column. Close these cells downward in their input columns. If row height is
measured from the bottom, the total input mass satisfies

`j <= sum_{r=1}^{2*f} r = f*(2*f+1)`.

The target receives at least `2*f` marks. After column sorting, at least f of
them are outside its bottom f rows, so `E >= f`.

If `n >= (2*f+1)/delta`, the input obeys `j <= delta*f*n`. Universal semantic
Property F requires the strict inequality `E < epsilon*j`, hence necessarily

`epsilon*(2*f+1) > 1`.

For `epsilon=1/86000000`, this forces `f >= 43000000`. A distinct-key input
realizing the binary threshold exists by assigning its largest j ranks to the
marked cells. The first column sort preserves this threshold pattern.

Quantifiers: the scramble is fixed first, then the input is chosen adversarially.
This directly challenges the all-input contract. The obstruction is relevant
to arbitrarily large widths; it does not assert failure at every small width.
The geometry has `m=2*f+64*b`, so the required height condition is available.

Choosing k rows instead gives escaped/input ratio at least
`2*(k-f)/(k*(k+1))`. This particular bound is maximized at integer
`k=2*f` or `2*f+1`, where it equals `1/(2*f+1)`.

## Consequences

The earlier f≈131040 one-scramble target is impossible under the current F
contract for sufficiently large n. Improving witness counting or rounding
cannot fix it. A conjectural one-round error `O(log(f)/f^2)` is also incompatible
with this universal-in-width obstruction at fixed epsilon scale.

The current proof's billions-sized sufficient condition still leaves room above
this millions-sized necessary condition. However, at the scheduler template
ratio `f/m=4095/2^37`, f>=43000000 requires
`m >= 43000000*2^37/4095 > 2^50`. Its bitonic budget then uses k>=51:
one scramble costs coefficient at least 1326 in that budget, and two scrambles
with three full column sorts cost at least 1989. These are budget limitations,
not lower bounds on arbitrary sorting networks.

## Several rounds: the obstruction changes

The same inverse construction can be traced through t scrambles and exact
column sorts. Keep desired threshold marks in the bottom `2*f` rows. Pull back
through each row permutation and downward-close at each preceding column sort.
The last pullback costs at most `f*(2*f+1)` marks; each earlier pullback multiplies
mass by at most `2*f`, since every desired mark remains within those rows.
The final target still has at least f escaped marks. Thus, when n is sufficiently
large for support, this argument only forces

`epsilon*(2*f+1)*(2*f)^(t-1) > 1`.

For two scrambles this obstruction is of square-root scale in `1/epsilon`,
rather than linear. This does not prove existence at that scale. It does show
why requiring the first round alone to meet F is the wrong interface for a
smaller two-round construction. This extension remains unaudited beyond the
explicit backward-closure argument.

## Revised next step

Prove F for the complete two-scramble pipeline directly. Allow large first-round
fringe error; use second-round dispersion to obtain the final relative-rank
bound. Trace reduced escaping witnesses through both rounds, retaining their
shared row and column constraints instead of multiplying unrelated worst-case
counts. Pair this with the separate two-round bulk lemma.

Alternatively weaken the scheduler's required epsilon or increase its fringe
fraction, but then re-prove the hierarchy invariant and charge the changed
round count. Under 1000 and 200 remain unproved targets; the current one-round
small-fringe route cannot establish them.
