# The 64-cell / 4096-packet interface

Research audit by Codex (GPT-6), 2026-10-15. The calculation below is
hand-derived, not a global sorting theorem.

The conditional 197.5 accounting uses 26 merges of two **4096-wire** sorted
packets (13 layers each) and 57 layers of reassembly. The checked sender
repair uses **64-wire** rank cells, with their two 32-wire halves. These
contracts cannot be identified without a change-of-scale argument.

In particular, small variance of large-packet threshold counts does not
imply small variance of the 64-cell counts inside their sorted outputs.
Suppose each sorted large packet has exactly 2048 ones. Large-packet count
variance is zero. Its 64 consecutive 64-cells have counts

```
0, ..., 0, 64, ..., 64       (32 copies of each).
```

Their common mean is 32 and their centered squared-count energy is 65536
per large packet. The new sender repair does not increase this energy, but
it does not make it small either. Thus its zero fresh repair-energy defect
does not itself pass the 4096-packet mixing estimate into the next stage.
This example is an interface obstruction, not a counterexample to the
proposed sorting construction.

More generally, split a sorted `64*K`-wire Boolean packet with `X=64*q+r`
ones, `0<=r<64`, into `K` consecutive 64-cells. Their counts have sum `X`
and sum of squares `64*X-r*(64-r)`. Their energy about `X/K` is exactly

```
64*X - X^2/K - r*(64-r).
```

The next useful mathematical interface should therefore preserve the
**sorted profile**, rather than treating all small cells as approximately
equal to the large-packet mean. Two possible routes are:

1. Carry 4096-packet labels through ports, explicitly price partial large
   packets, and compare their selected counts to the ideal sorted profile
   with the same source mean. Charge perturbations to mixed large-packet
   count deviations, not to the intrinsic 0/64 small-cell variation.
2. Define phase-specific potentials before splitting and after reassembly,
   with an explicit transfer operator between them. Its deterministic
   baseline must account for sorting within each large packet.

There is a simple candidate estimate for route 1. In a sorted `m`-wire
Boolean packet with `X` ones, the number selected by a rank interval
`[a,b)` is

```
f_[a,b)(X) = min(b-a, max(0, X-(m-b))).
```

It is monotone and 1-Lipschitz in `X`. For any partition of the packet into
fixed rank intervals, and `X>=Y`, all selected-count differences are
nonnegative and sum exactly to `X-Y`. Consequently their aggregate absolute
deviation is exactly `|X-Y|`; splitting a sorted profile creates no new L1
perturbation relative to the corresponding ideal sorted profile. The same
holds for unions of partition pieces assigned to destination ports.

`PacketProfile.lean` now kernel-checks the ideal cell-count formula and the
exact L1 identity for these equal 64-rank cells (`profileCell_formula`,
`profileCell_L1_exact`). More strongly, `profileCellMean_L1_exact` handles a
fractional common mean by interpolating the profiles at its floor and ceiling;
`profileCellMean_cohort_L1_exact` sums this identity over an arbitrary cohort
of packets, and `profileCellMean_cohort_L1_sq` bounds the squared cohort-wide
fine-profile error by cohort size times the coarse packet-count energy. This
is precisely the norm conversion needed to feed the finite matching-cycle
L2 estimate into an aggregate fine-profile L1 budget, assuming that estimate's
input/output counts are represented by the sorted packet profiles. The
aggregate 64-cell profile error equals the aggregate 4096-packet count error
exactly. Thus, for this profile potential, there is no change-of-scale loss
before port selection. It still needs to connect to the
actual sorted packets and a common bag/rank target, and destination reassembly
must be shown to transform the profile with a controlled error. This does
not supply the unbounded matching family or global rank contraction.
