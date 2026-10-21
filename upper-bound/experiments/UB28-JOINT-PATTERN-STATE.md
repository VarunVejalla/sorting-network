# UB-28 joint-pattern state: research sketch

Status: the joint histogram matching formulas and the conditional split
kernel are exact for the exchangeable annealed law used by the first-moment
argument. A simpler block-count state is sufficient for this law. For a
fixed-input analysis, histogram data alone does not justify the split kernel.

## Scope of the split law

For a fixed input, equivariance of a random matching kernel does not by itself
make the output distribution exchangeable. For example, with two positions
and three block rows, columns `(000,001)` and `(001,000)` have the same joint
histogram but split into opposite ordered child profiles. If the two matched
rows are all zero, a random matching leaves the third row's positional
pattern unchanged. This is a real caveat for fixed-input probabilities.

It does not invalidate the first-moment recurrence. That recurrence averages
over a uniform input and the random schedule. The joint law is invariant
under independent permutations of wire slots within each block: uniform
matchings are equivariant under those relabelings, and a physical split
preserves the subgroup acting independently within child blocks. Therefore
conditional on the block-count vector, block patterns are independent
uniform subsets. In particular, the joint column sequence is exchangeable,
and the multivariate-hypergeometric split kernel below is exact for the
annealed law. The block-count process is the simpler exact state for this
purpose.

Here is the matching step explicitly. For one paired pair of width-`h`
blocks, let the incoming one-sets be `A,B`, and let a fresh uniform matching
be a bijection `pi` from left slots to right slots. The output one-sets are
`C={i in A : pi(i) in B}` on the left and `D=B union pi(A)` on the right.
For any slot permutations `sigma,tau`, the map
`(A,B,pi) -> (sigma(A),tau(B),tau o pi o sigma^{-1})` preserves the law
conditional on `|A|,|B|` and sends `(C,D)` to `(sigma(C),tau(D))`. Conditional
on output counts, `S_h x S_h` acts transitively on all pairs of output
subsets of those sizes. Thus `(C,D)` is uniform on that Cartesian product,
which is precisely conditional independence of the output patterns. This
also remains true after mixing over possible incoming counts, conditional on
the outgoing count vector. A split has the analogous property: given child
counts `l,r`, each pair of child subsets corresponds to one parent subset of
size `l+r`, so a uniform parent subset induces independent uniform child
subsets. Applying these steps to disjoint pairs/blocks proves the product
invariant by induction. Fresh independent matchings and the annealed uniform
input are essential assumptions.

The width-2 example in `UB28-TOP-HEAVY-SCHEDULE.md` rules out a block-count
state for a fixed input conditioned on its exact patterns. It does not rule
out the count state for the annealed first moment. A joint histogram may still
be useful as a refined entropy state for one terminal inversion: its backward
dependency cone has only finitely many blocks at each dyadic scale, even
though each block's width grows.

For a tuple of `k` supported blocks, write the wire-column type at position `t`
as `v_t in {0,1}^k`, and let `H_v` count positions of each type. The candidate
state is the histogram `H=(H_v)`, together with the exact ordered block labels
and finite pairing/edge phase. A fresh uniform cross-matching is equivariant
under a common permutation of all coordinate slots: conjugating each matching
permutation by the common relabeling preserves its uniform law. Thus equal
histograms in the same labeled geometry have the same next-histogram law for
that randomized matching step. This lumpability statement does not imply that
the output sequence is uniform over its histogram orbit.

At a physical half split, if the incoming sequence is exchangeable conditional
on `H`, retain the **joint allocation** of every row type to the first and
second halves. Under that extra hypothesis, the allocations have the
multivariate-hypergeometric law; the pair of child histograms remains coupled
through the shared allocation. This distinguishes
the width-2 counterexample: aligned singleton blocks have histogram `{00,11}`,
while independent singleton blocks have `{01,10}`. Replacing either by two
separate block counts loses the relevant information.

The histogram state is exact for a fixed, phase-tagged support geometry across
the randomized matching step, but is not yet a full-network state. Erasing
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

Conjugation makes this independent of the chosen representative. There is a
closed exact count for each triple histogram, so no separate cycle enumeration
is needed. Write `H_b` for the input count of row type `b`,
`T_{abc}` for the number of slots whose predecessor/current/successor types
are `(a,b,c)`, and `M_{ab}=sum_c T_{abc}`. A triple table is feasible exactly
when its central marginal is `H_b` and its pair flow balances:
`sum_c T_{abc} = sum_p T_{pab}` for all `a,b`. The latter expresses that
the number of permutation edges from type `a` to type `b` is the same whether
counted at its source or target. The exact number of permutations producing
this table is

```text
N(T) = (prod_b H_b! / prod_{a,b,c} T_{abc}!) * prod_{a,b} M_{ab}!.
```

To see this, first assign each central type-`b` slot its predecessor and
successor type, in `H_b!/prod_{a,c}T_{abc}!` ways. For every edge type `(a,b)`,
then biject the `M_ab` sources of type `a` whose successor has type `b` to
the `M_ab` targets of type `b` whose predecessor has type `a`, in `M_ab!`
ways. These independent bijections construct exactly one permutation and
count every permutation once. Therefore the probability of the table is
`N(T)/h!`.

For fixed alphabet size `q=2^k`, Stirling's formula gives
`h^-1 log(N(T)/h!) = -I_T + O(q^3 log(h+1)/h)`, uniformly in feasible
tables, where

```text
I_T = H(p) + H(M) - H(T) = I(C ; A,B) >= 0.
```

Here `p_b=H_b/h`, `M_ab` is normalized by `h`, `T_abc` is normalized by
`h`, and `H( )` is Shannon entropy using natural logarithms. Pair-flow balance
makes the marginals of `A,B,C` all `p` and the `AB` and `BC` pair entropies
both `H(M)`, so the
displayed expression is the mutual information of successor type `C` with
the predecessor/current pair `(A,B)`. The output histogram is the
deterministic image `H'_d = sum_{a,b,c : F(a,b,c)=d} T_{abc}`. There are at
most `(h+1)^(q^3)` integer tables, hence for any specified output histogram
its probability is bounded by this subexponential factor times
`exp(-h * inf I_T)` over feasible tables with that output. The checker
`ub28-matching-triple-types.py` exhaustively verifies the exact factorial
identity for all 416 words of widths 1 through 5 over up to three colors.
It also verifies the induced two-bit comparator output kernel for all 256
four-slot words over the four two-bit types.

There is a convenient relative-entropy relaxation of the matching rate.
Under a feasible triple law `T`, pair-flow balance makes the `AB` and `BC`
marginals equal to `M`. Thus
`D(T || p tensor p tensor p) = I_T + I(A;B)`, while
`I(A;B)=I(C;B) <= I(C;A,B)=I_T`. Consequently
`I_T >= (1/2) D(T || p tensor p tensor p)`. If `F` is the local comparator
map, data processing gives

```text
I_T >= (1/2) D(F_*T || F_*(p tensor p tensor p)).
```

The second distribution is the zero-cost mean-field output histogram. This
weaker bound depends only on input and output histograms and may be easier to
optimize across the schedule.

Under conditional exchangeability, the physical half-split has an exact type
kernel. If parent type counts
are `H_v`, first-half allocations are `X_v`, and second-half allocations are
`Y_v=H_v-X_v`, then
`P(X)=prod_v binom(H_v,X_v)/binom(h,h/2)`. If `R_{uv}` counts the aligned
first-half type `u` and second-half type `v`, conditional on `X,Y` its
probability is
`prod_u X_u! prod_v Y_v! / ((h/2)! prod_{u,v}R_{uv}!)`.
The resulting child histogram is exactly `R`. Thus both matching and split
steps admit finite-type entropy rate functions on the joint state; this
removes the combinatorial-formula obstacle, but does not yet optimize their
composition or establish a rate above `ln 2`. The same checker verifies this
split formula for 103 parent words at widths 2 and 4.

## Reachable finite suffix obstruction (2026-10-21)

The width-128 exact suffix has an inversion at edge 508 for a six-block
profile with one-counts `(35,24,64,37,79,25)`. Its width-256 parent counts
are `(59,101,104,256)`, so the two offset passes can preserve this profile:
for each matching, pair all left-block ones with right-block ones. The
width-512 parent counts are `(160,360)` and admit the same preservation.
The fixed input is made genuine by putting zeros before the six profile
blocks and ones after them; the script
`ub28-exact-suffix-screen.py` now checks that the all-one suffix really is
present before using it as the final width-256 block.

For 70 random rounds at widths 256 and 512, the specified preserving event
has probability `10^(-9014.528)` (product of the exact factors
`binom(b,a)/binom(h,a)` for each paired block with counts `a<=b`). On that
event the exact width-128-to-1 suffix leaves the `10` at edge 508. This is a
valid lower bound on failure probability for this fixed input and schedule;
it only rules out treating the fixed suffix as universally sorting arbitrary
width-512 inputs. The probability is far too small by itself to challenge a
first-moment proof for one whole network.

The split's per-parent-column cost is explicit as well. Set `p_v=H_v/h`,
`x_v=X_v/h`, `y_v=Y_v/h`, and `r_{uv}=R_{uv}/h`, where the parent width is
`h` and each child half has width `h/2`. Feasibility requires
`x+y=p`, `sum x=sum y=1/2`, and `r` has marginals `x,y`. Put
`u=2x`, `v=2y`, and `w=2r`; then the log probability divided by parent width
is

```text
sum_a p_a H(x_a/p_a) - ln 2 - (1/2) I_w(U;V),
```

so its nonnegative cost is
`J_split = ln 2 - sum_a p_a H(x_a/p_a) + (1/2) I_w(U;V)`.
At the typical split `x=y=p/2` and `w=p tensor p`, this cost is zero.
More generally, the same expression simplifies exactly to
`J_split = (1/2) D(w || p tensor p)`: decompose this KL divergence into the
mutual information `I_w(U;V)` plus the two marginal divergences, and use
`(1/2)(D(u||p)+D(v||p)) = ln 2 - sum_a p_a H(x_a/p_a)`.
For a fixed terminal edge, a complete trajectory's normalized cost per
original wire is the initial `1/2 * D(p_top || uniform_4)` plus the sum of
each matching cost `I_T` and split cost `J_split`, weighted by that stage's
number of columns divided by `n`. Since the cone has at most six rows, each
stage has a fixed finite alphabet; the number of integer type paths over
`O(log n)` scales is `exp(O(log^2 n))`. Therefore a uniform infimum above
`ln 2` would suffice for the first-moment gate after absorbing these path and
Stirling errors. Computing or lower-bounding that coupled infimum is the
remaining quantitative problem.

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

The annealed block-count state already supplies the required split invariant.
The larger joint-histogram state is optional and may help derive a sharper
large-deviation operator. The remaining proof program is:

1. Formalize the annealed product-permutation invariant and exact count
   transitions for the specified schedule.
2. Bound the large-`h` local count transition by a certified method-of-types/
   entropy operator, preserving positivity and uniform finite-width errors.
3. Optimize the rate over every edge phase and boundary class for a schedule
   whose depth coefficient is below 300; require the bad-edge exponent to
   exceed `ln 2` with explicit slack.
4. Sum the subexponential trajectory and edge factors, then use the first
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
start before the certified rate and uniform error gates pass.

## Status correction

The proof-program paragraph above predates the annealed symmetry audit. The
uniform support bound and exact finite-type matching/split kernels are now
derived, and the simpler block-count recurrence is exact for the first-moment
ensemble. No separate permutation-cycle enumeration is needed for that
recurrence. The remaining gate is to certify the local trajectory cost over
all edge phases and boundary cases, prove it exceeds `ln 2` for a schedule
below coefficient 300, and control the finite-width errors.

## Fixed-cell Bellman screen: rejected as a useful certificate

An exploratory outer-cell max-plus prototype used fixed-width density bins,
interval upper bounds on matching entropy, and a
concavity bound on split entropy. For the central edge and the `(high,low) =
(260,20)` top-alternating schedule, it returned rate zero at both 2 and 4
bins for `n=2^14`. This is only ordinary binary64 numerical evidence, not a
certified computation; the temporary prototype was removed, so the screen is
not currently reproducible from the repository.

The relaxation is formally in the safe direction, but it is too loose: each
stage optimizes over every density in a cell independently. A maximizing path
can therefore choose one representative at the end of a stage and another at
the start of the next, even though no single density trajectory makes those
choices. Over `Theta(log n)` split stages, these resets can accumulate and
erase the rate. The zero output is consequently a vacuous bound, not evidence
against the underlying schedule. Fixing the conserved pair total during each
matching gadget does not fix this cross-scale issue.

The next viable certificate should use a potential evaluated at the actual
continuous local density profile. For each phase/stage, prove
`q_s(z,z') + F_{s+1}(z') <= F_s(z)` for every feasible transition, then
telescope. Interval cells can still certify each inequality, provided the
same continuous profile is shared across both sides of every transition. For
matching rounds, retaining the exact conserved total `gamma` gives the local
Bellman form
`W_r(gamma,alpha) >= sup_x (J(alpha,gamma,x) + W_{r-1}(gamma,x))`.
The exact width-16 anchor can supply the terminal potential. Any useful result
must still cover every edge phase and boundary class, certify entropy endpoints
with outward bounds, and leave strict margin above `ln 2` after finite-type
errors.
