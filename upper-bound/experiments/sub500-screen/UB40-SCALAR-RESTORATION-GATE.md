# UB-40 scalar restoration gate (2026-10-24)

**Status: model gate, not a sorting-network theorem.** This tests a necessary
piece of the periodic-restoration story against the actual scalar accounting
in R1 Lemma 4.3′. Reproduce with
`python upper-bound/experiments/sub500-screen/ub40_scalar_recurrence_gate.py`.

For fixed schedule and stranger-distance ratio `δ`, let `M` be the coefficient
in the order-zero outsider bound (`M·c`). Ignoring geometry charge `γ` for this
screen, Lemma 4.3′ gives the affine step

```text
M_next ≤ λ M + (r* + η ε_B)/ (Aν),
λ = (1 + (k−1) sib + δ A²k)/(Aν),
sib = δ k A²/(1 − δ²k²A²).
```

The interval table in `screen.py` gives the local error `ε_B` for cheap and
precise stages. At the screened `(k,A,ν)=(16,64,1/8)` point with cheap-stage
tolerance `T=1000`, fringe idealized away, and a `q_prec=24` refresh, the
reproduced values are approximately

```text
M_base = 7.56e−6, λ = 0.125128
ε_cheap = 4.494e−2, ε_precise = 1.897e−5.
```

One precise step after seven cheap steps leaves `M≈8.08e−4`, about 107 times
the base bound. So the existing UB-40 model's *single* refresh does not close
even this scalar restoration contract. Four consecutive precise steps after
ten cheap steps return `M≈5.31e−6 < M_base`; the periodic mean-depth screen is
`((10·3S(9)+4·3S(24))/14)·(5/6) = 294.64`.

Compatibility obstruction: after ten cheap stages, `M?6.43e-3`. The existing
Lemma 4.4 support condition is `M c <= delta_F f n`, while protected-fringe
geometry requires `(f+1)n <= pi*c/2`. Even with maximal `f n <= pi*c/2`,
the certified `delta_F=1/8` gives a support cap of only `7.57e-6`, so the
relaxed profile exceeds it by about `850x`. Even allowing `delta_F=1` leaves
it over the geometric cap by about `106x`. No choice of `f` repairs this
mismatch. More strongly, starting at the support cap, one transition can use
at most `epsilon_B?4.57e-5` and remain below it; the screen's `T=1000` error
is about 980 times larger. The cached bulk table then needs integer row
exponent `q>=23` (three-sort stage cost about 690 per log bit before other
charges), so a scalar invariant that must retain the existing fringe-support
cap at every cheap stage cannot deliver the sub-300 cost.

The conditional cost point therefore needs a structural change: separate the
large, short-range separator error from the long-range outsider mass that must
fit in the fringe support, or prove a new provider that avoids this support
condition. It also needs the all-order/rank-profile recurrence, geometry charge,
and exact startup/terminal schedule. The scalar calculation identifies both a
possible order-zero reset cadence and the interface that currently prevents
turning that cadence into a sorter.

The support obstruction is per-stage in the existing Lean bridge, not just a
restriction used in final accounting. `R1T.P_all` inducts through every stage
using `realStageKernel`; its `fringe_send_real_gen` premise bounds the current
order-`r` outsider count by `Jmax`, and `NodeSpecAll` sets
`Jmax = delta_F * f * n`. Restoring scalar `M` only at refresh stages therefore
cannot justify the intervening cheap-stage fringe sends. A periodic proof
must either keep a separate long-range outsider component below this cap at
every stage, or replace the fringe-send lemma/provider so it accepts the
larger temporary count. This conclusion follows from the current Lean
interfaces, independently of whether the scalar numerical cycle is sharper.

## Why the current local contract cannot simply drop the support cap

There is a direct abstract obstruction to proving a larger-`J` fringe-send
bound from `NodeSpecAll` alone. For example, take `a=16`, `pi=8`,
`Jmax=1`, ancestor interval `[0,16)`, and a bag `K=[32,48)`, with the local
network sorting `K` exactly. Then its two cut-error fields have `EB=0`. Its
`fHigh`/`fLow` properties hold with zero escapes at `j=1`: the locally highest
key occupies only the highest output position, and the locally lowest key
occupies only the lowest. Yet all 16 keys are outsiders to the ancestor
interval, and the middle output window `[4,12)` sends 8 outsiders to children.
Thus exact local sorting plus the present small-fringe promise does not imply
a useful send contraction when the total outsider count exceeds `Jmax`.

This example is a legal countermodel to the *local contract implication*, not
a trace of the scheduled global network. It isolates what an UB-40 repair
must add: a global alignment condition relating each bag's key set to its
static ancestor interval, or a recentered/rank-defined ancestor state. Merely
adding all-cut B bounds, or summing the existing `fHigh`/`fLow` guarantees up
to `Jmax`, cannot recover that missing relation. The economical next gate is
to state such a rank-alignment state and prove one transition with a separate
short-range spill and long-range outsider term; if the term is not contractive
through cheap stages, the 294.64 scalar cadence is not a viable UB-40 route.


Round-one distance-tail diagnostic: the interval certificate `cert_walk_n.py`
from read-only branch `ub-34-fringe-duality`, run at `m=512`, maximum possible
margin `W=512`, and target `7.56979e-6`, returned an upper bound
`4.04239e-3` (`cert_tail_q9.out`). It therefore cannot certify the existing
fringe support at cheap `q=9`, even when the margin spans the entire row
height. This is a failure of the available round-one certificate, not a lower
bound on the true tail and not a screen of the full two-round network. A
useful distance-graded invariant needs a sharper full-stage tail provider.

## Tail-profile replacement interface (2026-10-26)

The exact missing local statement is now isolated by the kernel-checked
`sent_outside_le_of_tail_profile` in
`upper-bound/experiments/runaware/AKS/Chvatal/StrangerBounds.lean`. It replaces
the scalar `Jmax` premise by upper and lower rank-prefix escape bounds for
every `j <= |K|`, expressed as a tail function `T(j)`. It proves that the
middle-window outsiders sent from a bag are at most
`T(Hhi) + T(Hlo)`, where `Hhi/Hlo` are the actual counts above/below the
ancestor interval. The old lemma is recovered in spirit when `T(j)=εF*j`,
but the new form also supports an additive short-range spill term or a
distance-graded profile.

This removes the *formal support-cap requirement* from the send inequality;
it does not produce the needed provider. `NodeSpecAll.fHigh/fLow` only give
the proportional bounds through `Jmax`, and the UB-34 margin-crossing tail
certificate does not directly bound these rank-prefix position escapes. A
candidate provider must establish the all-`j` profile on the actual separator
and keep its summed forcing compatible with the periodic scalar recurrence.
Until that provider exists, the 294.64 mean-cost cycle remains only a model.
