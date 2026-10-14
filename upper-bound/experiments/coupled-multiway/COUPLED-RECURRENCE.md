# Coupled recurrence: aggregate displacement and actual fresh-error sum

Status: hand-derived arithmetic and candidate interfaces, not a checked
sorting-network theorem. The source parameters are the current Chvatal `§7`
schedule and the direct-multiway profile candidate. The exact source locations
are `upper-bound/best/AKS/Chvatal/Schedule7.lean`,
`upper-bound/best/AKS/Chvatal/StageKernel.lean`,
`upper-bound/experiments/direct-multiway/ProfileWeights.lean`, and
`ProfileStageKernel.lean`.

## Aggregate count from boundary displacement

Let the ordered target windows have rank cuts
`R_j = pi/2 + j*tau`, for `j=0,...,63`, and let the native address cuts be
`A_j = L + sum_{i<j} c_i`. Here `c_i` is the number of keys assigned to child
address interval `i`, and `L` is the number of relevant keys below the parent
interval. For each interior cut, the number of keys whose native child and
rank window disagree is bounded by `|A_j-R_j|`: a key contributes to the
misclassification count only if it lies between those two cuts. Summing by
cuts gives the safe aggregate

```text
total interior child-window mismatches <= sum_{j=0}^{63} |A_j - R_j|.
```

Writing `delta_i = c_i-tau`, the exact displacement is
`A_j-R_j = (L-pi/2) + sum_{i<j} delta_i`, hence

```text
sum_j |A_j-R_j|
  <= 64*|L-pi/2| + sum_{i=0}^{62} (63-i)*|delta_i|.
```

This is the useful vector-valued interface: it charges a child count defect
according to how many later cuts it displaces. It is not yet a scalar bound in
the checked `O, rho` variables: that requires the schedule's exact mass
identity connecting `L`, the opposite fringe, `sum_i c_i`, and the parent's
outsider count. End cuts and keys in the two fringes must also be bounded and
added separately; the displayed sum only covers interior cuts.

Two checks prevent an incorrect “charge once” shortcut. If `c_i=tau`,
`pi` is even, and all `pi` parent outsiders are below the parent interval,
then `L=pi`, so every cut has displacement `pi/2` and the aggregate is exactly
`32*pi`. Thus parent outsiders can be charged at many cuts. Also, the earlier
uniform per-child screen `64*O + 4032*rho - 32*pi` is consistent with this
example; any sharper aggregate theorem must preserve that `32*pi` behavior or
explain a compensating term from the schedule's mass identity.

For a candidate scalarization, let `D=L+R-pi` be the total fringe-mass defect,
where `R` counts keys above the parent interval. Then
`|L-pi/2| <= pi/2 + |D|/2`. If the exact child-mass equation also gives
`sum_i delta_i = -D`, and only positive child defects have independent bounds
`delta_i^+ <= rho_i`, then
`sum_i |delta_i| <= 2*sum_i rho_i + |D|`. A deliberately conservative result
is therefore

```text
sum_j |A_j-R_j|
  <= 32*pi + 126*sum_i rho_i + 95*|D|.
```

This follows from replacing every coefficient `63-i` by 63. It is not known
to improve the uniform `4032*rho` term when all 64 `rho_i` equal `rho` (it
gives `8064*rho`); its value is that it retains the displacement vector and
can be sharper when defects occur late or are localized. Do not use the
scalarized inequality until the exact mass identity and fringe endpoint terms
are supplied by the actual schedule.

## Weighted active-level capacities

For the candidate global potential, take level weight `a=1/128`. At stage `t`
and level `i`, there are `64^i` bags and each has capacity
`capacity(d,i,t)=64^d*4096^i*64^(-t)/4096`. The aggregate weighted capacity is

```text
W(d,i,t) = 64^i * a^i * capacity(d,i,t)
          = n * 2^(11*i - 6*t - 12),   n=64^d.
```

The active levels satisfy `i <= omega7(t)` and the parity condition from
`Schedule7.lean`. Dropping the lower-bound and parity restrictions only
increases the sum. Since `W(d,i+1,t)/W(d,i,t)=2048`,

```text
sum_{i active at t} W(d,i,t)
  <= (2048/2047) * n * 2^(11*omega7(t)-6*t-12).
```

For `t=0,1`, the exponents on the right are `-12,-7`. For `t=2,...,7` they
are `-2,3,-14,-9,-4,-21`; thereafter each residue class modulo 6 drops by
14 in the exponent. Summing these actual stage envelopes over all `t>=0`
(and hence over the finite actual range `t<=tf7(d)`) gives

```text
sum_t sum_{i active} W(d,i,t)
 <= (4329599/519938) * n < 8.328*n.
```

This rational constant is a direct geometric-series calculation from
`omega7`; it has not yet been formalized in Lean. It is stronger than applying
the per-stage bound `8.01*n` uniformly for `O(d)` stages.

## Price of rank-zero additive errors

In `StageKernel`, the rank-zero fresh bulk and schedule-drift terms on each
target child are `(invEpsB+slackCoeff)*C_parent`, with
`invEpsB=1/59,000,000` and
`slackCoeff=(4096-128+1)/(2*4096^2*64^2)`. Summing these over 64 children and
using level weight `a=1/128` multiplies the parent's aggregate weighted
capacity by `64a=1/2`. Consequently their sum over all actual stages and
active parent levels is bounded by

```text
(1/2)*(invEpsB+slackCoeff)*(4329599/519938)*n
  < 1.909e-7*n.
```

The rank-zero sibling source is different: it is bounded using the local
profile (`63*mu*siblingFactor*C_parent` in the source), so it is a coupling
term proportional to the local invariant, not fresh error independent of
that invariant. With the current profile scale `122/125`,
`profileEffectiveDelta=(1/5300000000)*(483/500)`, and the source
`profileSiblingFactor`, its summed coefficient under the same weighted
capacity bound is `< 4.665e-8*n` if the local profile cap is available at every
active parent. The multiplication by 64 children and level-weight ratio is
again `64a=1/2`.

Thus the two rank-zero additive sources (bulk tolerance plus schedule slack)
are at most `1.909e-7*n` over the full schedule. The local-profile sibling
forcing contributes at most `4.665e-8*n` under its stated hypothesis. These
absolute totals alone do not prove terminal purity: a coupled recurrence must
show how each stage's local forcing contracts and how aggregate transfer
depends on the local profile.

## Rank-positive channel and recurrence interface

For rank `r>=1`, the fringe source `epsF*S_parent(r)` is profile-proportional,
not an independent additive constant. With level weight `a` and rank weight
`b`, its child-send factor includes `64*a*b= b/2`; the profile envelope then
adds the geometric rank factor `profileEffectiveDelta`. The exact rank sum
must be derived together with the chosen definition of the global potential;
the local profile candidate has `b=608,000,000`, and `b*delta_eff<1` is
checked in `ProfileWeights.lean`. The existing higher-rank transfer screen
`64*epsF*z + 64/z` at `z=a*b=10,000` is only a coefficient screen, not a
schedule-summed forcing theorem.

A useful sound interface should state, for every actual stage `t`,

```text
L_(t+1) <= lambda*L_t + eL_t
G_(t+1) <= rho*G_t + kappa*L_t + eG_t,
```

where `L_t` is the maximum normalized local rank profile over active bags,
and `G_t` is the weighted aggregate profile over active bags/ranks. It must
include explicit support changes as levels enter/leave the active range,
all rank-zero and rank-positive channels, and the exact per-stage error sums.
The local rank-zero row is nearly saturated in the current candidate:
`profileRankZeroTransfer*profileScale + profileRankZeroError` is about
`0.975866` versus `profileScale=0.976`; the higher-rank transfer coefficient
is about `0.999886`. A new stage must preserve or improve those margins.

The next mathematical step is to prove the boundary-vector estimate and the
active-level sum as standalone lemmas, then derive `eL_t,eG_t` from the actual
sender placement. The work here gives a plausible accounting target, not a
closed coupled recurrence or an improved upper bound.
