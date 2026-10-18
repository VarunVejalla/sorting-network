# Checked bag recurrence: transfer audit

Status: algebraic extraction from the checked Chvatal induction; **not** a new
sorting bound or a proof of a weighted-kernel contraction.

## State and capacity normalization

In `upper-bound/best/AKS/Chvatal/StageKernel.lean`, for a bag `b`, let
`S_b(k)` denote `b.strangers k ...`; its invariant uses the shifted index
`S_b(r+1) <= mu delta^r C_b`, where `C_b = capacity d b.l t`.
The next stage's capacity is exactly `64 C`, with
`C = capacity d (b.l - 1) t`:

```text
capacity(d, b.l, t+1) = 4096*(1/64)*C = 64*C.
```

This shift matters: the parent fringe estimate takes rank `r` on the parent
and contributes to rank `r+1` on the child.

## What the checked inequalities say

Write `P_r` for the parent's `strangers r`, `Q_k` for the next bag's
`strangers k`, and `C` for parent capacity. Placement splits `Q_k` into its
parent-send and children-send parts.

For `k=1`, `StageKernel.hBadSend0` and `.hFromChildren0` give

```text
Q_1 <= P_1 + 63*mu*siblingFactor*C + epsB*C + slackCoeff*C
       + mu*delta*64*4096^2*C.
```

The induction hypothesis gives `P_1 <= mu*C`. `cond42_scaled` proves that
the resulting right side is at most `mu*(64*C)`, the next-stage rank-1
budget. This is an affine bound with several sibling/flow terms.

For `k >= 2`, put `r=k-1`. The checked parent fringe inequality and the
induction hypothesis give

```text
parent-send part <= epsF*P_(k-1)
                  <= epsF*mu*delta^(k-2)*C.
```

The checked children-send inequality is already specialized to the old
geometric invariant:

```text
children-send part <= mu*delta^(k)*4096^2*64*C.
```

Therefore `cond45_scaled` verifies

```text
epsF*mu*delta^(k-2)*C + mu*delta^k*4096^2*64*C
    <= mu*delta^(k-1)*64*C.
```

After division by the positive target scale, the two fractions of the budget
are

```text
parent contribution:   epsF/(64*delta)
children contribution: delta*4096^2.
```

The exact rational inequality in the source is
`epsF/64 + delta*4096^2 <= delta`. Thus the parent channel consumes about
96.3% of the available rank-`k` budget and the children channel about 0.32%;
the remaining margin is about 3.4%. These decimals are explanatory only; the
Lean theorem uses rationals.

## Why this is not yet the desired matrix

The source-set argument in `StrangerBounds.strangers_children_le` contains a
more informative inequality before it applies `OutsiderBoundLe`: the
children-send contribution to target bag `b` at rank `k` is at most the sum of
the old rank-`k+1` counts in its 64 child bags. This follows from
`strangers_child_eq` and the union bound. Similarly, the parent-send
contribution to child `b` at rank `k>=2` is at most `epsF` times the old
rank-`k-1` count in its parent bag. Thus the rank-`k` transport channels have
the formal shape

```text
Q_b,k <= epsF * P_parent(b),k-1 + sum_{c child of b} P_c,k+1,  k >= 2.
```

This is a candidate refinement of the current scalar theorem: the current
`StageKernel` stores the children side only after `StrangerBounds` has
substituted the geometric invariant. The union-bound generalization itself is
straightforward, but it is not presently stated as a theorem in the package.
Rank 1 remains exceptional: its parent channel is the `BadSend` estimate and
includes parent outsiders, sibling contamination, bulk error, and slack.

For a global potential summing bag/rank counts with positive weights
`w_(level,rank)`, the two displayed transport channels suggest the adjoint
coefficient condition, away from boundaries,

```text
64*epsF*w_(level+1,k+1) + w_(level-1,k-1) <= rho*w_(level,k).
```

The factor 64 comes from one source bag feeding its 64 child bags; it must be
checked against the exact placement schedule and any overlap/double counting.
This is a candidate inequality, not yet a proved closed recurrence. The
remaining refined state/kernel must also account for:

1. each child's rank-profile contribution to a parent bag;
2. sibling contamination of the rank-1 channel;
3. parent-to-child fringe leakage, including its rank shift;
4. capacity/geometry scaling and the boundary/leaf cases.

There is a striking preliminary signal in the interior transport terms. If
rank-1 and boundaries are temporarily omitted and weights vary geometrically
with level, `w_(level,rank)=t^level * v_rank` with constant `v_rank` makes the
two displayed contributions sum to

```text
64*epsF*t + 1/t.
```

For `epsF=1/86,000,000`, this expression is minimized at
`t=1/sqrt(64*epsF) ~= 1159.2`, with value
`2*sqrt(64*epsF) ~= 0.001726`. Thus the interior two-way transport alone
admits a very strong weighted contraction. This is **not** yet a global
potential result: the level weights change by a factor of about 1159 per
level, and it is unknown whether the exceptional rank-1 errors, finite
boundaries, stage activation, and initial/final potential conversion remain
controlled. It is nevertheless a concrete reason to test the joint-level /
rank potential before abandoning this route.

That small factor is for an **unnormalized global sum over bags**, with rank
1 and forcing omitted. It should not be conflated with the
capacity-normalized maximum below: a global sum has a separate conversion
problem because the number of bags and their capacities both grow rapidly
with level.

The minimal useful formal interface is likely a **vector-valued stage
contract** whose hypotheses bound each send component by a nonnegative
linear combination of the relevant parent/child profile coordinates, plus an
affine local-error vector. Then the checked bag induction can establish the
weighted potential theorem from a finite rational inequality
`w^T K <= rho*w^T`, `rho<1`. This contract must still be realized by one fixed
oblivious comparator network and its actual scheduler.

## Immediate research decision

Do not search for weights against a guessed matrix. First expose the
rank-profile union bound as a generic lemma, then include the exceptional
rank-1 sibling/bulk-error row and all boundary cases in the level/rank
recurrence. Solve the resulting finite rational adjoint inequalities. The
isolated rank shift is not by itself an obstruction: the question is whether
weights can control both opposing rank/level shifts and the exceptional
rank-1 row, while keeping the weighted local-error budget small. If not, add
the rank reset/repartition state or use a multi-stage/block potential.

That is the concrete feasibility test. Only after it yields a closed kernel
should we solve for weights and decide whether a jointly designed multiway
stage has plausible depth below the current `T<400` drop-in gate or the
ambitious new-schedule coefficient below 200.

## Finite weighted-max calculation (conditional)

Normalize each bag profile by its capacity,
`X_b,k = S_b(k)/capacity(d,b.l,t)`. If `C` is the parent-level capacity,
then the next-stage child capacity is `64*C`, while each old child capacity
is `4096^2*C`. The proposed generic children lemma therefore gives, for the
children-send part, `4096^2 * max_child X_child,k+1` after normalization.
The parent-send part is `epsF/64 * X_parent,k-1` for `k>=2`; at rank 1,
`hBadSend0` instead gives `(1/64)*X_parent,1` plus the local error.

Consider the weighted maximum
`M = max_(bags b, ranks k>=1) a^b.l * q^(k-1) * X_b,k`, temporarily
excluding the root and handling it as a separate boundary obligation. The
row sums of this candidate transfer operator are bounded by

```text
rank 1:       a/64 + 4096^2/(a*q)
rank k >= 2:  epsF*a*q/64 + 4096^2/(a*q).
```

For the exact current rationals, the concrete choice `a=1/2`, `a*q=304,000,000`
(`q=608,000,000`) gives row bounds approximately `0.063001` and `0.110421`.
The higher-rank minimum over `a*q` is
`2*sqrt(epsF*4096^2/64) ~= 0.1104`. Also `q*delta ~= 0.114717`, so under the old geometric envelope
`X_b,k <= mu*delta^(k-1)`, the weighted state is bounded by `mu/2` on
non-root levels. The rank-1 local error is

```text
(63*mu*siblingFactor + epsB + slackCoeff)/(64*mu)
    ~= 0.969036
```

of that weighted budget at the worst level. Adding it to the rank-1 row gives
about `1.03204`; adding it to the higher-rank row gives about `1.07946`.
Neither closes a contraction with the current local error and `mu` budget.
Even the optimal higher-rank weight ratio leaves a factor about `0.1104`,
while the existing order-0 local error alone consumes about `0.9690` of the
budget. This rules out this particular one-step weighted-max repair using the
current constants; a useful variant must materially reduce the order-0 local
error, change the state/budget, or amortize errors over a multi-stage block.

There is also a weight-independent two-coordinate obstruction for the
transport operator. The normalized fringe channel sends `(level 1, rank 1)`
to `(level 2, rank 2)` with coefficient `epsF/64`; the children channel
sends back with coefficient `4096^2`. For any positive weights on these two
coordinates, the two weighted row coefficients have product exactly
`epsF*4096^2/64`, so their maximum is at least its square root, greater than
`0.055`. For the candidate geometric weights above, rank 1 controls the
old-envelope scale and the local error leaves less than `0.031` for
transport, so that candidate cannot close. A different weight profile could
let a higher-rank coordinate dominate the old-envelope scale and buy more
error room; whether it can do so uniformly in `d` while retaining a useful
conversion back to per-bag bounds remains an open finite-inequality problem.

This does not yet improve the proof. The bound `hBadSend0` is supplied by
`BadSendField`, whose construction uses the full old `OutsiderBoundLe` to
bound sibling contamination by `siblingFactor`. The proposed weighted
maximum does not imply that old scalar invariant uniformly over levels:
`a<1` makes the reverse conversion worsen with level. Keeping both
invariants merely re-proves the old result. To make the potential structurally
useful, the next theorem must replace the scalar-invariant use inside the
order-0 sibling estimate by a bound stated in terms of the weighted profile,
or else prove a second level/profile envelope that is closed alongside the
weighted maximum. The root row and all finite-level activation cases also
remain to be checked.

The generic child-profile union bound is in [`ProfileLemma.lean`](ProfileLemma.lean).
The more relevant generic subtree estimate is in
[`ProfileSibling.lean`](ProfileSibling.lean): it bounds bad keys in a subtree
by a sum of per-bag, per-rank profile bounds, without assuming
`OutsiderBoundLe`. Exact rational checks are in [`ProfileWeights.lean`](ProfileWeights.lean).
These scratch declarations were kernel-checked with the locally installed
Lean 4.29.0-rc4 executable and existing `.olean` artifacts; Lake package
synchronization was bypassed because the local mathlib checkout reports a URL
mismatch. No change was made to dependency state.

## Explicit rank-profile recurrence for the BadSend sibling row

Let (B_r) bound `strangers (r+1)` by (B_r C), where (C) is the bag's
capacity. The index (r=0) is the exceptional bad-send coordinate. With
(A=4096^2), the child-capacity and 64-child union bound give the normalized
transport rows

```text
rank 0:  B'_0 <= B_0/64 + A*B_1 + (63/64)*S(B) + (epsB+slack)/64
rank r:  B'_r <= (epsF/64)*B_(r-1) + A*B_(r+1),  r >= 1
```

The profile-sensitive sibling mass at the parent capacity is

```text
S(B) = 4096 * sum_{h odd, h>=1} (64*4096)^h * B_h.
```

This follows from the checked generic subtree theorem: at depth `h`, there are
`64^h` descendant bags, their capacity is `4096^(h+1)` times the parent
capacity, and only odd `h` contribute by the occupied-level parity. The old
scalar proof is the special case `B_h = mu*delta^h`, which gives
`S(B) = mu*siblingFactor`. `Jmax` is retained if every `B_r <= mu`.

An exact rational geometric profile closes these rows for the current
constants:

```text
B_r = c*mu*theta^r
c = 122/125 = 0.976,   theta = delta*(483/500).
```

For `r >= 1` the transfer multiplier is
`epsF/(64*theta) + A*theta < 1`. The rank-zero row reduces to

```text
c * (1/64 + A*theta
     + (63/64)*4096*(64*4096*theta)/(1-(64*4096*theta)^2))
  + (epsB+slack)/(64*mu) <= c.
```

Both rational inequalities are kernel-checked in `ProfileWeights.lean`. The
scale `c` is about 2.4% below the old rank-zero allowance. This is an
invariant-feasibility result only; it does not change the depth coefficient.
In fact this candidate is pointwise below the old geometric envelope, so the
old invariant can still be recovered and used for `Jmax`.

The counting bridge is now formalized in
[`ProfileKeysBelowChild.lean`](ProfileKeysBelowChild.lean):
`keys_below_child_profile` repeats the disjointness, wire-count, and
one-child cardinality calculation, but returns the explicit finite profile
sum `profileBadMass` in place of `mu*siblingFactor*capacity`. It was checked
with the local Lean executable. This is the precise replacement interface
needed by `BadSendField.hM_keys`.

The parity/geometric collapse and BadSend integration are now in
[`ProfileBadSendField.lean`](ProfileBadSendField.lean). It proves
`profileBadMass_geometric_le`, then a scratch `badSendField_profile` theorem
whose only outsider hypothesis is the geometric profile. The theorem does
not assume `OutsiderBoundLe`; Lean confirmed the scalar hypothesis was
unnecessary even in the first compiling version. The old scalar estimate is
still used by the separate fringe-send/Jmax and child-send parts of the
promoted stage proof.

This closes the specific `BadSendField` sibling-control obligation, but not
the stage invariant. The remaining integration is to generalize the
children-send rows in `StageKernel` from their hard-coded geometric
consequences, prove initialization and propagation of the geometric profile,
and re-establish the fringe/Jmax conditions from that profile (or a derived
scalar corollary). No sorting coefficient has changed yet.

## Rank-1 sibling term unfolded into the profile

The scalar `siblingFactor` is hiding a concrete transfer channel. For a bag
`w`, let `Desc_h(w)` be its descendant bags exactly `h` levels below it and
let `S(z,r)` be the raw count of order-`r` strangers in `z`'s registers. Since
the registers partition `subtreeKeys(w)`, and for `z in Desc_h(w)` being
non-native to `w` is precisely being an order-`h+1` stranger in `z`, we have
the profile identity

```text
badSubtree(w) = sum_(h=0..d-w.level) sum_(z in Desc_h(w)) S(z,h+1).
```

This is the unsummarized form of the argument in `Lemma41Real.subtree_bad_le`:
that theorem applies the scalar outsider invariant to each summand and then
replaces the resulting profile by a geometric series. In the active parity
case used for sibling contamination, only odd `h` occur. Thus, for a parent
`u` and child `w_j`, the number of keys in `u`'s registers addressed below
`w_j` has a bound of the form

```text
down(u) + Delta(u,j) +
  sum_(h odd) sum_(z in Desc_h(w_j)) S(z,h+1),
```

where `Delta(u,j)` is the finite cut/occupancy defect. This replaces the old
`down + Delta + mu*siblingFactor*capacity` bound before it is collapsed by
`OutsiderBoundLe`.

To carry that information through `bad_send0_real`, its current uniform
premise `nativeCount(j) <= down + rho` should be generalized to per-child
defects `rho_j`. The desired all-cuts conclusion is a bound for each output
child using the sum of the *other* child defects, and, crucially, a joint
bound after summing the output errors over all 64 children. The `fromParent`
wire sets are disjoint, so the source-position intruder contribution can be
aggregated across children. However, parent rank-1 outsiders also shift the
ordered address/rank boundaries and may contribute to many child mismatches;
disjointness alone does not show that they are charged once. The current
`NodeSpec`/`BadSend` interface only states separate per-child bounds, and an
aggregate estimate must retain cumulative boundary displacement.

### Conditional transfer-matrix screen

Assume that joint allocation lemma, the per-child fringe bound, and the
profile-form child-union bound. Use raw stranger counts and the aggregate
potential

```text
Phi = sum_(bags b, ranks r>=1) alpha^(b.level) * beta^(r-1) * S(b,r),
z = alpha*beta.
```

For one 64-way level transition, the candidate weighted-column contributions
are:

| Channel | Weighted contribution |
|---|---:|
| Parent rank-1 outsider / cumulative boundary displacement | current per-child theorem gives up to `64*alpha` in the joint weighted sum |
| Parent fringe error to 64 children, shifting rank by one | `64 * epsF * z` |
| Child profiles aggregated to their parent, shifting rank down by one | `1/z` |
| A fixed sibling-subtree profile coordinate into the other 63 output children | `63/z^(r-1) <= 63/z` when its rank `r-1` is odd |

The higher-rank arithmetic (`64*epsF*z + 64/z < 0.014` at `z=10000` and
`epsF=1/86,000,000`) remains a useful screen, but the rank-1 source column
needs a larger coefficient. The tempting estimate
`alpha + 64*epsF*z = 0.507442` at `alpha=1/2` assumes an invalid once-only
charge. Summing the existing per-child theorem gives a conservative `64*alpha`
coefficient on parent outsiders (plus the child-defect and finite-error
terms). The equal-count, one-sided-outsider example below realizes about
`32*alpha` of this, so the true coefficient is not one. A weighted-`l1`
contraction is not ruled out by this correction: for example, the conservative
coefficient would be at most `1/2` if `alpha <= 1/128`. But this makes the
level weight much smaller and does not resolve fresh-error accumulation or
terminal conversion. The fixed-coordinate sibling accounting can still be
better than the earlier bagwise weighted-max test.

This does not yet close the induction. Three independent obligations remain:

1. Prove an aggregate ordered-window theorem with cumulative defects and
   outsider balance. The current hypotheses allow the parent-outsider
   mismatch to recur across many cuts, so disjoint output sets alone do not
   reduce its coefficient to one.
2. Bound the weighted fresh error from cut/occupancy defects and separator
   bulk misses over **all active bags and stages**. The current equal-block
   schedule has the nonzero `slackCoeff`; the tapered no-slack flow proposal
   is a model, not a checked flow table. The `0.014` number prices only the
   linear transport, not this forcing term.
3. Convert the aggregate potential to zero impurities in every terminal
   leaf, uniformly in tree depth. With `alpha<1`, a uniform global potential
   bound alone does not give a depth-independent lower bound for an impurity
   in a deepest leaf. A new schedule needs a terminal-weight conversion or a
   local-plus-global two-potential invariant.

So the refined rank-1 channel is promising enough to pursue, but it is not a
closed recurrence and it does not yet establish a coefficient below 500. The
next useful theorem is an aggregate ordered-window bound retaining cumulative
cut displacement and per-child defects; it will determine the actual rank-1
coefficient and whether the profile transfer matrix can be made contractive.

### Exact joint decomposition to target

The proof of `bad_send0_real` gives a useful exact decomposition, but not yet
the desired aggregate estimate. For each child `j`, write `W_j` for keys
output from the parent's `j`-th block. Its bad rank-1 keys are contained in

```text
{k in W_j : rk_K(k) is outside rank-window j}
  union
{k in K : rk_K(k) is in rank-window j, k is not native to child j}.
```

The first sets are disjoint across `j` because the `W_j` are disjoint, and
`NodeSpec.intruder_keys` bounds each by `2*EB`; hence their total is at most
`128*EB` (and can potentially be sharpened by a simultaneous intruder
guarantee). The second sets are disjoint across `j` because the rank windows
are disjoint. They are independent of the particular output permutation:
they count sorted ranks whose keys lie outside the corresponding child
address interval. Thus summing `bad_send0_real` is not the right proof; it
would count the parent's outsider set 64 times. Instead, the required new
lemma is an aggregate sorted-window estimate for

```text
sum_j |{k in K : rk_K(k) in window_j, k not native to child j}|.
```

It should use the *vector* of native child counts `c_j` (or defects
`rho_j = max(0,c_j-down)`), rather than replace it immediately by
`max_j rho_j`. Since child address intervals and sorted ranks are both
ordered partitions, this is a one-dimensional boundary-displacement count:
each key in the sum crosses at least one boundary between the rank-window
partition and the address partition. The proof needs to quantify the total
boundary displacement from the cumulative sums of `c_j`, while separately
accounting for parent outsiders and the two half-fringe regions. The current
`BW.window_wrong_le` only proves a per-window estimate from the uniform
`rho`; it does not imply the needed aggregate estimate at the desired cost.

### Boundary-displacement calculation and a necessary correction

For the aggregate window term, set `c_i` to the number of keys of `K` in
child-address interval `i`, and let `L` be the number of keys below the
parent interval. At the cut before child `j`, the address partition has
cumulative count

```text
A_j = L + sum_(i<j) c_i,
```

while the equal rank-window partition has cut
`R_j = pi/2 + j*tau`. Since both partitions are ordered, the number of keys
whose address class and rank-window class differ is at most the sum of the
cut displacements `sum_j |A_j-R_j|` (with the two endpoint/fringe cuts
handled separately). This gives a clean route to a vector-defect lemma, but
it also exposes a serious obstacle: parent outsiders affect *all* cumulative
cuts, not just one destination child.

In particular, even with zero child-count defects (`c_i=tau` for all `i`),
take even `pi` parent outsiders all below the parent interval and none above
it. If `pi/2 <= tau`, each of the 64 rank windows starting at
`pi/2+j*tau` contains `pi/2` keys from the preceding address class (the first
window takes these from the outside fringe; later windows take them from the
preceding child). The aggregate address/rank mismatch is exactly `32*pi` in
this idealized count model. Thus the present hypotheses do **not** allow the
parent rank-1 outsider mass to be charged only once. The earlier
`alpha`-coefficient entry in the candidate transfer table was too optimistic:
it assumed the very joint estimate we needed to prove, and the ordered-count
calculation shows that estimate is false without an additional balance/locality
guarantee on the outsiders or a different invariant that prices cumulative
boundary displacement. The table should be treated as a diagnostic target,
not a valid transfer bound under the current `NodeSpec` contract.

For comparison, summing the existing uniform per-child bound gives at best
`64*O + 4032*rho - 32*pi` for the rank-window component, where `O` is the
parent outsider count and `rho` is the uniform child-count excess; this is
just the sum of the 64 separate estimates, not a new sharp aggregate theorem.
In the zero-defect, one-sided-outsider example (`O=pi`, `rho=0`) it gives
`32*pi`, matching the boundary-displacement calculation. A promising revised
stage contract would control the left/right outsider split or directly bound
the weighted sum of cumulative cut displacements.

The actual local toolchain is present. `elan` does not register the populated
toolchain directory, but its direct executable reports Lean 4.29.0-rc4. The
focused command `lake build AKS.Chvatal.BadSendReal` succeeds through the
direct Lake binary after passing temporary per-process Git
`safe.directory` settings for the root and shared package checkouts. Lake
replayed 1,921 cached jobs and completed successfully. This checks the existing
module; the new aggregate boundary analysis above is still a paper argument,
not a Lean theorem.
