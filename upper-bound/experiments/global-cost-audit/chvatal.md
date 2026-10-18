# Chvátal global cost audit

Source audit: 2026-10-10. This note records checked facts from the current
`upper-bound/best` source and conditional research budgets. It proves no new
sorting bound.

## Checked cost identity

For `N = 64^d`, [`DepthSkeleton.lean`](../../best/AKS/Chvatal/DepthSkeleton.lean)
defines

```text
ordinaryRounds d = 3d - 21
totalDepth d = 6320 + (3d - 21) * 3540 + 903
             = 10620d - 67117.
```

Since `log₂ N = 6d`, an ordinary stage of depth `C` contributes exactly
`C/2` to the limsup coefficient. The root `6320` and final `903` are additive
and asymptotically free. The checked endpoint therefore has coefficient
`3540/2 = 1770`; see
[`Chvatal1830Final.lean`](../../best/AKS/Bounds/Chvatal1830Final.lean).
The ordinary `3540` is two full bitonic column sorts at height `m <= 2^59`:
one sort costs `59*60/2 = 1770`, and
[`RealNets.pack_depth_le`](../../best/AKS/Chvatal/RealNets.lean) charges twice
that. Small nodes are fully sorted within the same budget. Thus changing the
root or final cleanup cannot improve the coefficient.

The complete conditional budget, if the existing scheduler and its proof are
retained, is:

| desired limsup coefficient | required ordinary-stage depth |
| --- | ---: |
| `< 1000` | `< 2000` (integer depth at most `1999`) |
| `<= 1000` | `<= 2000` |
| `< 200` | `< 400` (integer depth at most `399`) |
| `<= 200` | `<= 400` |

For the present one-scramble `sort–scramble–sort` pack at height `2^k`, the
stage charge is `k(k+1)` and the coefficient is `k(k+1)/2`. Hence `k=44`
just reaches coefficient `990`, while `k=45` costs `1035`. For a two-scramble
pipeline with the intermediate sort shared, the honest charge is three sorts,
`3k(k+1)/2`, and the coefficient is `3k(k+1)/4`; see the construction accounting
in [`chvatal-two-round-separator.md`](../../../docs/chvatal-two-round-separator.md).
It is below `1000` through `k=36` (coefficient `999`; `k=37` gives `1054.5`),
and no full-sort construction with `k >= 23` can reach `200`.

## What the global proof actually consumes

[`NodeSpec.lean`](../../best/AKS/Chvatal/NodeSpec.lean) requires one fixed
network to satisfy, for every permutation input, four simultaneous statements:

1. `bHigh` and `bLow`: at all 65 scheduler block boundaries, bulk rank error is
   at most `EB`.
2. `fHigh` and `fLow`: for every `0 < j <= Jmax`, fewer than `eps*j` extreme
   keys escape the outgoing half-fringe.

The instantiated values are

```text
EB = paperOrdinaryEpsB * a / 2,  paperOrdinaryEpsB <= 1/59000000,
eps = 1/86000000,
Jmax = floor((128/4095) * (up/2)).
```

These values are visible in
[`KernelSetup.lean`](../../best/AKS/Chvatal/KernelSetup.lean),
[`StageKernel.lean`](../../best/AKS/Chvatal/StageKernel.lean), and
[`Lemma62Ratio.lean`](../../best/AKS/Chvatal/Lemma62Ratio.lean). The consumers
are the actual induction fields proved in `BadSendReal/Field` and
`FringeSendReal/Field`; an average-error separator cannot be substituted.
In particular, `j <= 86000000` forces zero fringe escapes because the
inequality is strict.

The present existence proof needs `m >= 2^58` for bulk concentration and, when
the fringe is nonempty, `f >= 85*10^8`; these hypotheses occur directly in
[`GeneralParams.lean`](../../best/AKS/Chvatal/GeneralParams.lean) and
[`NodeGeom.lean`](../../best/AKS/Chvatal/NodeGeom.lean). Scheduler geometry
can have fringe ratio only `f/m = 4095/2^37`. Moreover, the deterministic
one-round adversary forces `f >= 43000000` for this universal relative-error
contract, independently of sharper probability estimates; see
[`chvatal-fringe-obstruction.md`](../../../docs/chvatal-fringe-obstruction.md).
At that ratio even the one-round bitonic budget needs `k >= 51`, hence
coefficient at least `51*52/2 = 1326`. Constant search inside the current
one-round interface cannot cross `1000`.

## Two-round route and its real budget

The most credible current route is to prove the bulk and fringe guarantees
jointly for the complete two-round pipeline, then feed that network directly to
`NodeSpec`. The conditional variance/Bernstein calculation in
[`chvatal-two-round-separator.md`](../../../docs/chvatal-two-round-separator.md)
suggests bulk accuracy near `k=42`, but its displayed calculation uses bulk
tolerance `1/59000000`. The exact `NodeSpec` allowance is
`paperOrdinaryEpsB`, which is only proved *at most* `1/59000000`; the displayed
calculation therefore does not yet establish the exact checked contract. A
usable theorem needs a tighter tail calculation at `paperOrdinaryEpsB`, or a
reparameterized global `specEB` proof. Geometry and rounding may also require
`k=43`. Three full sorts at `k=42` cost depth `2709` and coefficient `1354.5`.
The small-rank analysis in
[`chvatal-two-round-small-ranks.md`](../../../docs/chvatal-two-round-small-ranks.md)
shows why this is structurally better than forcing first-round Property F:
under its stated support hypothesis, first-round concentration into a wider
fringe deterministically gives zero final escapes for `j <= 86000000`; the
two-round adversary only forces `f >= 8031`.

This separates two targets:

* A sub-1000 theorem needs either a joint two-round separator already valid at
  `k <= 36` (depth `<= 1998` at `k=36`, coefficient `999`), or a `k≈42`
  construction whose final operation is replaced by a shallow repair. At
  exactly `k=42`, two full sorts cost `1806`, leaving repair depth at most `194`
  for coefficient `<=1000`, or at most `193` for coefficient `<1000`. If
  `k=43` is required, two sorts cost `1892`, leaving at most `107` for the
  strict target. These are budget ceilings, not evidence that such repairs
  exist. In addition, the current small-node fallback costs `2016`, already
  exceeding the strict `1999` stage budget, so it too must be sharpened or its
  threshold/handling changed.
* A coefficient near `200` requires ordinary depth at most `400`. At `k≈42`,
  even one full bitonic sort costs `903`, so it requires a new shallow
  approximate partition/repair primitive and probably a co-designed stranger
  invariant. No refinement of the current full-sort probability constants can
  meet this budget.

## Concrete missing theorem

The useful next theorem is not another local concentration estimate in
isolation. It is an existence theorem, uniform over the four scheduler node
geometries, of a fixed two-round comparator network satisfying the exact
`NodeSpec a up down net (specEB t a) (specJmax up) eps` contract, with ordinary
depth at most `1999` for a strict sub-1000 result (ideally `400` for coefficient
at most `200`). Its proof must provide simultaneously:

* both orientations and all 65 bulk boundaries;
* every rank `0 < j <= specJmax up`, including the zero-escape small-rank range;
* one common pair of scrambles, rather than witnesses chosen separately per
  cutoff or guarantee;
* the physical comparator implementation and its charged repair depth;
* a replacement for the last full column sort with a precise semantic
  contract sufficient to reprove both bulk and fringe output counts;
* a small-node fallback within the same stage budget.

The present modular sub-obligations are (i) a finite, uniform two-round bulk
tail theorem from the variance argument, (ii) a joint two-round relative-fringe
theorem for ranks above the deterministic small-rank range, and (iii) a shallow
repair network realizing the second-round redistribution. Replacing a column
sort is not a depth-only substitution: the existing bulk and fringe counting
arguments use fully sorted columns. The repair contract must state exactly
which threshold counts and extreme-rank placements it preserves, and the two
probability proofs must be rerun against that contract. Item (iii), together
with this compatibility proof, is the decisive sub-1000 cost question. For the
aspirational `200` target, the theorem must be paired with a revised global
invariant if the exact current accuracies cannot be achieved in depth `400`.

## Verdict

The checked `1770` decomposes cleanly as `3540/2`, and the scheduler makes the
local contract much stronger than bulk mixing. A sub-1000 result is
conditionally plausible only if a joint two-round theorem reaches the exact
bulk tolerance and supplies a repair within the `193`-depth strict budget at
`k=42` (or `107` at `k=43`), while also replacing the `2016`-depth small-node
fallback. No such repair theorem is currently known. A coefficient near `200`
needs a different local primitive and likely a simultaneous scheduler redesign.
The highest-value work is therefore the exact joint two-round `NodeSpec`
theorem with an explicit semantic repair contract and depth parameter, not
further search over the current one-round constants.
