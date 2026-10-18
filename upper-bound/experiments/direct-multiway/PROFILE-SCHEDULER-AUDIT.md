# Profile-to-scheduler audit

Status: exact depth accounting and feasibility analysis; no new sorting bound.

## What the profile changes

`Profile_P_all` strengthens the rank envelope used by the existing Chvatal
schedule. It changes the allowed stranger counts, but does not change the
schedule's number of rounds, the separator network at each round, or the
terminal block size. The checked purity argument still needs the final rank-2
stranger count to be below one in every terminal bag.

The current schedule has `3d - 21` ordinary rounds, each of depth 2838, plus
fixed root and leaf costs 6320 and 903. Since the input size is `64^d`, its
asymptotic coefficient is

```text
(3 * 2838) / log2(64) = 8514 / 6 = 1419.
```

Thus improving only the profile constants cannot improve 1419. For a direct
gain, the profile must justify a cheaper separator at each ordinary round, or
fewer rounds per fixed amount of growth.

## Required per-round savings

If the same schedule and terminal theorem can use an ordinary separator of
depth `2838 - s`, then its coefficient becomes

```text
3 * (2838 - s) / 6 = 1419 - s/2.
```

Consequently a target coefficient `C` requires saving at least `2*(1419-C)`
layers from every ordinary separator. This means 838 layers for `C=1000`,
1838 for `C=500`, and 2438 for `C=200`. The current profile theorem does not
give a route to those savings: it is an error invariant, while the 2838 cost
comes from the serial comparator layers in the separator pack.

## Can we stop the schedule earlier?

Stopping a fixed number `q` of ordinary rounds early leaves blocks larger by a
factor `64^q`. Sorting those larger blocks adds a fixed cost when `q` is fixed,
so it does not change the asymptotic coefficient. Stopping a positive fraction
of the rounds early makes the final block size exponential in `d`; a generic
bitonic final sorter then has quadratic-in-`d` depth, so this does not yield a
finite logarithmic coefficient. A useful early-stop scheme would need a new
linear-depth terminal sorter together with a purity theorem at its larger
leaves.

## Concrete next proof obligation

The profile can help only if it feeds a construction theorem. The smallest
useful target is a profile-parameterized separator interface that states,
for each candidate reduced-depth pack, its growth factor, all-rank output
profile, fresh error, and exact terminal implication. Then reprice the pair
`(depth, log2 growth)` using the recurrence in `RECURRENCE-BUDGET.md`. Merely
substituting the tighter geometric envelope into `BadSendField` preserves the
existing 2838-layer pack and therefore preserves coefficient 1419.

At present there is no proved cheaper pack, no justified reduced-round
schedule, and no improved coefficient from the profile work. The high-upside
research target remains a new separator/repair construction whose profile
guarantees allow it to remove serial sorting work, rather than only tightening
the error budget around the existing work.
