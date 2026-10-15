# Sender-local half-packet repair and the variance interface

Derived by Codex (GPT-6), 2026-10-15. The scalar inequalities below are
kernel checked in `PacketRebinning.lean`. `PacketSenderCycle.lean` and
`PacketCountBridge.lean` now check the shifted sender's actual support cycle,
six-layer parallel repair, exact executed count formula, and sender-relative
energy bound. The destination packet partition and subsequent coarse/fine
recurrence remain open. No sorting-network coefficient is proved here.

## A repair potential with no fresh boundary term

For a sorted Boolean packet of length `2h` with `x` true entries, its suffix
half contains `F(x)=min(h,x)` true entries and its prefix half contains
`G(x)=(x-h)_+`. Thus `F(x)+G(x)=x`, and both functions are monotone.

If every suffix half is paired once with a prefix half, after choosing output
labels by the suffix packet, the count transformation is

```
y_i = F(x_i) + G(x_(sigma(i))),   sigma a fixed permutation.
```

Unchanged full packets are fixed points of `sigma`. The scalar Lean model is
`halfRebin h x sigma`. It proves:

* Exact conservation: `sum y = sum x`.
* For every integer `u`, `sum (y_i-u)_+ <= sum (x_i-u)_+`, and the analogous
  negative-spill inequality. Hence aggregate absolute deviation does not
  increase.
* `sum y_i^2 <= sum x_i^2`.
* For **every real** reference `u`,
  `sum (y_i-u)^2 <= sum (x_i-u)^2`.
* Counts bounded by `2h` remain bounded by `2h`.

The positive-spill proof splits the reference as `F(u)+G(u)` and uses
subadditivity of positive part. Permuting the `G` terms preserves their sum;
monotonicity gives
`(F(x)-F(u))_+ + (G(x)-G(u))_+ = (x-u)_+`.

For the square bound, `F(x)G(x)=h G(x)` (either `G(x)=0` or `F(x)=h`).
In a repaired packet the cross term satisfies
`F(x_i)G(x_sigma(i)) <= h G(x_sigma(i))`. Sum, reindex by the permutation,
and use exact count conservation to obtain the centered real inequality.
This proof does not introduce a separate per-boundary rounding allowance.

These are sender-relative bounds: they remain valid around the sender's old
mean, including a nonintegral mean. They do not say that regrouping packets
from different senders preserves the sum of within-destination variances.

## The actual source ports implement a 65-cycle

Use packet length 64, half-width `h=32`. For a sender of size
`a = up + 64*down`, write

```
r_j = up/2 + j*down,       j = 0,...,64.
```

Suppose `up` is even, `down` is a positive multiple of 64, and `up/2` is
32 modulo 64. Every `r_j` is at the center of a packet. The 65 boundary
packets are distinct, with indices `p_j=floor(r_j/64)`. Their half-packets
are paired as follows:

* Child port `j<64` takes the suffix half of packet `p_j` and the prefix
  half of packet `p_(j+1)`.
* The parent port takes the suffix half of packet `p_64` and the prefix
  half of packet `p_0`.

Consequently the repaired counts on these 65 packets are exactly a cyclic
`halfRebin` transformation. Every other source packet remains intact.
Each repair support consists of different physical wires, including repairs
which take opposite halves of the same original boundary packet. Thus all
65 repairs can run in parallel in six generalized layers, and repairs of
different source bags are disjoint as well.

This sender-local formulation may be easier than receiver-by-receiver
pairing: it directly supplies the complementary-half permutation needed by
the potential theorem. The receiver still needs a packet partition and
capacity proof after collecting the outgoing packets.

The degenerate cases must be included explicitly. If `up/2` is packet
aligned, no half-packet repair is needed. If `down=0`, all wires return to
the parent and the logical packet partition can remain unchanged, even when
the two parent fringe intervals meet halfway through a packet. Positive
`down<64` is excluded by `64 | down`. Root/empty cases still need their
actual `FlowSizes` hypotheses instantiated.

The sender-local cycle description is now kernel checked. In
`PacketSenderCycle.lean`, `senderRepair_support_cycle` and
`senderRepair_boundary_cover` give exact support identities;
`senderBoundaryCell_packet` and `senderBoundaryCells_disjoint` identify the
65 distinct original packets. `scheduled_senderRepair_exists` supplies the
ordinary scheduled size hypotheses. In `PacketCountBridge.lean`,
`senderRepair_rebin_count` proves the exact count identity, and
`senderRepair_count_exists` packages the input-independent six-layer network
with sorting, count and energy conclusions. Its count theorem is for Boolean
inputs satisfying the packet invariant. A combined evolving packet placement,
whole-source partition and degenerate
cases still need to be composed; this is not the complete packet scheduler.
`senderRepair_count_at_threshold` already transfers the Boolean count
contract to every value threshold of the same fixed network.

## Consequence to test in the coupled recurrence

After mixing a sender, use its mean `mu_s` as the reference. If its outgoing
rebinning has the permutation representation above, its total centered
packet energy does not increase. Therefore the pure half-packet repair part
of the previously unspecified port defect has checked bound **zero** on the
65 affected cells of a shifted positive-down sender, under its packet-sorted
premise. Unaffected whole packets still need to be added to the partition.
The change of reference when packets enter destination bags remains.

Let destination `b` receive `k_sb` packets from sender `s`. For an outgoing
packet write its count as `mu_s + z_p`. Put

```
c_b       = sum_s k_sb,
bar_mu_b  = (sum_s k_sb*mu_s)/c_b,
xi_b      = (sum_(p -> b) z_p)/c_b.
```

Its actual mean is `bar_mu_b + xi_b`. Subtracting this mean gives the exact
within-bag energy identity

```
V_b' = sum_(p -> b) (mu_source(p) - bar_mu_b + z_p)^2 - c_b*xi_b^2.
```

Dropping the nonnegative final term and applying Minkowski across all
destinations yields the derived interface

```
sqrt(V_new) <= sqrt(V_sender_rebin) + sqrt(V_between),
V_between   = sum_(s,b) k_sb*(mu_s - bar_mu_b)^2.
```

Here the affected-cell part of `V_sender_rebin <= V_after_mix` follows from
the executed sender repair theorem; the complete source partition and
destination incidence are still to be supplied. The selected-packet mean
errors `xi_b` remain; they are not zero merely because full packets are
transported. Their bounds should use source-centered energy and the exact
packet incidence matrix. Controlling `V_between`, target drift, and coarse
rank error is the next mathematical gate. This calculation does not close
the two-scale recurrence or supply the uniform matching family.
