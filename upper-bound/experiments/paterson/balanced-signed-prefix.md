# Balanced signed-prefix control: invariance, slack, and reservoir exchanges

Status (2026-10-10): informal structural lemmas and sufficient scalar bounds,
with exact rational arithmetic in `signed_prefix_budget.py`. No improved
network or sorting coefficient is established.

## 1. Protected-only comparisons cannot balance the signed discrepancy

Recall the boundary statistic from the joint allocation audit:

    s(theta) = # protected keys below theta - # assigned protected prefix slots.

For fixed protected wire set and fixed slot assignment, **every comparator
network acting only on protected wires leaves s unchanged**, at every
threshold. The first term depends only on their value multiset; the second
is a fixed integer. Sorting or exchanging these protected keys can improve
which individual bag contains each key, but cannot balance this global prefix
statistic. Likewise, sorting the pool alone leaves it unchanged.

To change `s`, the construction must transfer keys between protected wires
and pool wires, or alter the protected set/slot assignment. Input-dependent
assignment is not an available oblivious-network shortcut. Removing a fixed
core does change the protected multiset, but the core must be constructed so
its removal has the required effect for every admissible input.

This is stronger than saying a balancing lemma is missing: it rules out
protected-only balancing as a way to prove that lemma.

## 2. Balance and local contamination are separate requirements

Even `s=0` at every boundary does not imply that each protected bin is pure.
Equal numbers of opposite-direction keys can cross a boundary and cancel
in `s`, while remaining local strangers. A successful balancing scheme must
control both residual bag errors and boundary discrepancies.

For one rebuilt level-4 bag and one ancestor threshold level, let `B` be its
stranger budget, `b` its protected-subset errors, and let `s_lo,s_hi` be the
signed discrepancies at that ancestor interval's boundaries. The sorted-pool
transfer argument gives the sufficient estimate

    rebuilt errors <= b + 2D + (-s_lo)_+ + (s_hi)_+.

Use the existing deep-error bound `2D <= (32/35) B`. If

    b <= beta B,     |s_lo|,|s_hi| <= gamma B,

then preserving the invariant follows from

    beta + 2 gamma <= 3/35.

For example, `beta=gamma=1/35` suffices. The parameters must be certified
uniformly at every ancestor level, not just at native-half thresholds. Half
purity remains exact and uses the stronger zero-deep-error argument.

The input invariant permits a protected original bag to start at its full
budget `B`. Even perfect signed balancing supplies no generic proof that its
remaining errors fit alongside the pessimistic deep-error term. Some local
purification, a sharper joint error bound, or a new invariant is still needed.
These sufficient conditions are not necessary conditions for every repair.

## 3. What simple residual filtering would have to achieve

Consider a design retaining protected subsets only from the sixteen original
level-4 bags, while pooling the original level-2 and root/cold registers.
Suppose each retained leaf contracts *every* relevant ancestor stranger count
by a factor `epsilon`:

    each protected leaf has at most epsilon B_L errors at ancestor level L,

where `B_L=mu*delta^(4-L)*C*A^4` is the common per-leaf budget. Require this
for all levels 1 through 4; native-half purity uses a separate exact argument.

For either ancestor boundary, the absolute signed discrepancy is bounded
by the total number of protected keys outside their assigned ancestor bins,
at most `16 epsilon B_L`. Any one protected rebuilt leaf contributes at
most `epsilon B_L` local errors. A rebuilt leaf's pool portion is a subset
of the ordered pool run assigned to its ancestor interval, so the same two
boundary bounds apply to it. Hence a conservative sufficient condition is

    epsilon + 32 epsilon + 32/35 <= 1,
    epsilon <= 1/385.

This avoids assuming any cancellation. It explains why merely retaining a
few-percent contamination is insufficient for this particular worst-case
proof. It does not establish a universal lower bound on residual error.

The existing separator error is approximately .0438354. Squaring it gives
.00192154, below `1/385`. Thus two correctly composed residual-filtering passes
are arithmetically strong enough for this conservative target. But the
existing primitive costs 989 per pass, already 1978 before pool sorting.
Composition must remove/protect extracted cores and recheck support and
fringe sizes at all ancestor cohorts; repeatedly applying the separator to
the original whole bag does not justify squaring the error.

Cheap half-halvers can contract errors too, but their retained pool may grow
substantially. The full size/depth recursion is needed alongside this error
inequality. A depth-only calculation does not certify a cheaper repair.

## 4. What a reservoir exchange would need

At a boundary, positive `s` means too many low keys remain protected; negative
`s` means too few. A comparison between one protected wire and one pool wire
can change the protected low-key count by one if the two keys straddle the
threshold and the comparator's output orientation selects the needed side.
Comparisons whose keys are on the same side make no change to that count.

For a protected leaf interval `[lo,hi)`, exchanging a low stranger for a pool
key inside that interval requires retaining the maximum at the protected
wire. Exchanging a high stranger for a native pool key requires retaining
the minimum there. After such an exchange, the pool probe may itself become
a stranger. Its initial purity is a consumable resource, not a reusable
threshold oracle.

A viable oblivious exchange lemma would need all of:

- Fixed protected/pool probe sets and admissible comparator orientations.
- A guaranteed supply of pool keys in the leaf's native interval.
- A matching/expansion condition ensuring sparse protected strangers meet
  enough still-native probes, uniformly over their unknown positions.
- Bounds on both remaining local strangers and `s` at every ancestor boundary.
- Pool-size, depth, and layout-error accounting after probes are consumed.

Counting strangers alone gives none of the matching or probe-supply claims.
In particular, one cannot choose the sign of a correcting exchange by reading
the numerical rank threshold at runtime.

## 5. Sorted-pool probes: a precise supply criterion

There is a useful conditional way to certify native probes. Let `r(q)` be
the pool-prefix slot count at boundary `q`, and suppose `|g(q)|<=D_q` and
`|s(q)|<=S_q`. Then the pool's true low-key count is in

    [r(q)-D_q-S_q, r(q)+D_q+S_q].

After sorting the pool, ranks `j` satisfying

    r(lo)+D_lo+S_lo <= j < r(hi)-D_hi-S_hi

are guaranteed native to the interval. Bounds are clipped to the pool's
index range. The guaranteed probe count is therefore at least

    max(0, r(hi)-r(lo)-D_lo-S_lo-D_hi-S_hi).

This is a fixed rank window given certified discrepancy bounds. It could
seed exchanges without inspecting an explicit threshold. However, using it
requires sorting the pool first; subsequent exchanges change its contents.
The proof must track which probes remain pure and whether a second pool
sort or another repair is needed. Such costs cannot be omitted.

The initial sparse half-concentration scheme gives no tight finest-boundary
`S_q`, so its attractive small pool does not automatically supply large
guaranteed finest-native windows. Proving those bounds is part of the target,
not a consequence of half purity.

## Assessment and next useful experiment

There is no current cheap balancing construction. The most concrete new
interface is a **native-reservoir exchange lemma** with the supply window
above and the two-output guarantees `b` and `s`. A worthwhile next experiment
would derive uniform probe supply from actual bag/cold allocation counts and
initial stranger bounds, then compare sparse matching costs with the available
repair budget. If probe supply is insufficient, concentrate a larger core or
relax the global invariant and recalculate its shrink factor.

The strongest conclusion so far is a method barrier: fixed protected-only
comparisons cannot improve signed-prefix balance, and balance alone cannot
replace local purification. Any proposed cheap repair must address both.
