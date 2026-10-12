# Conditional 945 candidate from a nonuniform Chvatal flow

Status: exact scalar arithmetic, separator probability screen, and an exact
real-valued **bounded-correction interior flow**; **not yet a sorting theorem**.
The unequal-width rank-window algebra, signed path reserve, and per-slot
transfer are kernel-checked in `VariableWindow.lean` and `SignedReserve.lean`
(see `PLAN-945.md`). The schedule-specific outsider invariant, integer
realization, and boundary cases remain open.

## Candidate and conditional price

Keep branching factor `k=64`, but use capacity growth `A=64` and stage shrink
`nu=1/16`. Use the existing two-scramble construction with target bulk error
`epsB=2^-21`, column-height floor `m=2^34`, and the existing fringe fraction
`dF=128/4095`. If a nonuniform flow removes the equal-block drift while
preserving the stranger induction, the scalar Chvatal conditions have the
following exact rational witness:

```text
mu   = 17/71,565,312
delta = 1/2^25
epsB  = 1/2^21
```

The candidate is attractive arithmetically because

```text
k*A = 64*64 = 4096 = 16^3.
```

The asymptotic schedule uses three ordinary stages per 64-fold tree scale.
Each ordinary stage costs `3*T(35)=1890` layers in the current three-sort
separator model. Since those three stages cover six input bits, the conditional
repeated-stage coefficient is `3*1890/6 = 945`. The earlier `+0.0053`
terminal-profile surcharge came from the now-discarded multiplicative profile
`pM^i`. The signed-debt recurrence restores uniform real occupancy, so the
surcharge should disappear if bounded integer rounding is proved. The
conditional price is therefore 945, not a proved bound.

The exact checks are reproducible with [`sub1000_screen.py`](sub1000_screen.py).
It verifies the separator and flow scalar inequalities below using `Fraction`, and verifies
the probability margins using the rational logarithm bounds already used by
the two-round bulk audit.

## Separator budget

Use the exact-mass, two-tailed (Variant B) form of the two-round bulk argument
from `upper-bound/best/notes/two-round/BULK2.md`. At `M=2^34`, take first-round
variance parameter `E1=38/10^6` and Bernstein parameter `lambda=1/80` for
the second round. With the existing upper bounds on `ln 2`, `ln(100)/16`, and
`ln(1000)/16`, the margins are:

```text
round 1: E1^2*M - ln(2(M+1)) - ln(100)/16 > 0.2596
round 2: M*K - ln(2(M+1)) - ln(1000)/16 > 0.8650
```

The monotonicity products are respectively greater than `24.8` and `25.5`,
so the estimates extend to every `m >= 2^34`. This is an arithmetic
specialization of the hand proof in `BULK2.md`; Variant B and this smaller
threshold are not yet Lean theorems.

For the fringe condition, the permitted recurrence error is
`epsF = A*nu*delta - A^2*k*delta^2 = 511/2^32`. The scheduled fringe ratio
gives more than `130,560` rows at `m=2^34`, above both the established `92,160`
row floor and `1/(656*epsF)`. `CandidateSeed.lean` now checks a two-stage
integer allocation with the required root and stage-two frontier sizes. The
network construction that realizes this allocation, its address placement,
and the outsider invariant at the stage-two seed are still unproved. Thus the
seed's cost is additive only if those special sorting stages have depth bounded
independently of `d`; this has not been established.

## Exact local flow that removes the drift

Write `Q=A^2*k^2`, and let `c` be the reference capacity of an interior bag.
The usual interior occupancy and upward flow have the forms

```text
a = (1 - 1/Q)*c
pi = (A*nu*k - 1)/Q*c = (nu/(A*k) - 1/Q)*c.
```

Instead of giving every child the same down-flow, propose these target child
sizes:

```text
end child:    c/k - nu*c/(2*A*k)       (two children)
middle child: c/k                      (k-2 children)
```

They conserve the available down-flow exactly:

```text
2*(c/k - nu*c/(2*A*k)) + (k-2)*c/k
  = c - nu*c/(A*k)
  = a - pi.
```

The endpoint reduction is `pi/2 + c/(2Q)`, so it tracks the half-fringe sent
up while retaining the small allocation reserve. The old equal child size was
`c/k - nu*c/(A*k^2)`. Giving every child that smaller size creates the
systematic `(k-1)*Delta2 - pi/2` term in the bulk estimate. In the proposed
flow, middle children receive the reference `c/k` size and only the two
fringe-facing children shrink. This is the concrete local mechanism intended
to remove that term.

At the candidate parameters the coefficients are dyadic:

```text
Q = 2^24
pi/c = 255/2^24
middle/c = 1/64
end/c = 2047/2^17.
```

**First attempt, now superseded:** keep one common upward-flow coefficient and
absorb the unequal split into a multiplicative address profile. The exact
profile is as follows. Let

```text
rM = 1/k
rE = 1/k - nu/(2*A*k)
rbar = (2*rE + (k-2)*rM)/k = 65535/2^22
pM = rM/rbar = 65536/65535
pE = rE/rbar = 65504/65535.
```

Then `2*pE + 62*pM = 64`. For a bag `v` at level `i`, define its reference
capacity to be the old scalar `c(d,i,t)` multiplied by the product of the
`pE`/`pM` factors along its address path. This profile satisfies the interior
capacity recurrence exactly. If `j` is the last edge type of `v`, then
`C(parent(v)) = C(v)/(A*p_j)`, while its children have capacities
`A*p_l*C(v)`. Consequently, with upward-flow coefficient
`s=nu/(A*k)-1/Q`,

```text
r_j*C(parent(v)) + s*sum_l C(child_l(v))
  = (rbar/A + s*A*k)*C(v)
  = (1-1/Q)*nu*C(v),
```

which is precisely the next-time occupancy `(1-1/Q)*C(v,t+1)`. The final
identity is the same exact rational mass identity as in the uniform schedule.
Thus the interior real-valued mass recurrence is closed; it is not necessary
to bound the position-dependent forcing by `mu`.

Integer rounding has two distinct errors that must not be conflated. Write
`d(v)` for the signed address debt in the real flow, and `eta(v)` for the
integer occupancy error relative to its real target. The ideal flows are
`up=s*C(v)-d(v)` and `down_j=r_j*C(v)+d(v)/64`; their sum is the real target
occupancy. Round the up-flow to an even integer (error at most one wire), then
allocate the remaining wires to the 64 child blocks. The sum of those integer
block sizes differs from the sum of their ideals by at most `|eta(v)|+1`.
If the shifted ideal block sizes remain nonnegative, balanced rounding with a
prescribed total can keep each block error at most
`1+(|eta(v)|+1)/64`. Each new bag receives one such parent-block error and at
most one wire of up-flow rounding error from each of its 64 children. Thus

```text
|eta(next)| <= 64 + 1 + (|eta(v)|+1)/64 <= 66.094 < 69,
```

when `|eta(v)|<=69`. The scalar inequality is kernel-checked in
`SignedReserve.lean`; `IntegerRounding.lean` now constructs an even natural
up-flow and 64 natural child blocks with exact total, conditionally on the
signed-debt, occupancy-error, and ideal flow split assumptions. It proves the
next occupancy error remains below 69 wires. The reference capacity lower
bound alone is insufficient: along an all-end address the real flow profile
shrinks, so one must stop splitting as soon as the actual bag falls below the
bulk threshold and sort it directly. The actual schedule must still establish
the hypotheses at each bulk step and handle root, frontier, and small-bag
cases.

The general Chvátal reference capacity is
`c=N*A^i*nu^t/(A*nu*k)`. For these parameters `A*nu*k=256`, so
`c(d,i,t)=2^(6d+6i-4t-8)`. This normalization matters: the legacy parameters
had `nu*k=1`, which made the denominator equal to `A`; that coincidence does
not hold here. A candidate pair of parity frontiers is

```text
alpha(d,t) = ceilParity(max(0, floor((2*t - 3*d + 23)/3)), t)
omega(d,t) = ceilParity(floor((t + 4)/3), t)
tf(d)      = 3*d - 20.
```

For `d>=14`, these meet at `alpha=omega=d-6` at `tf`; the reference capacity
at the meeting is `2^36`, matching the `64^6` native interval. In the ordinary
active band the alpha boundary has capacity at least `2^34`, and the omega
boundary at least `2^36`. The script's
integer scan over `d=14..300` checks frontier order, unit movement, and these
exponent bounds; the formulas are also simple enough for direct `omega`
proofs. The preceding terminal surcharge and adaptive termination argument
belonged to the discarded product-profile construction. Under the bounded
signed correction, reference capacities stay uniform across addresses, so the
terminal profile multiplier is absent in real arithmetic. To retain the 945
price, it remains to prove a uniform integer discrepancy bound and the
fixed-size terminal sorter rule. Neither is proved for all frontiers.

### Bounded signed correction: uniform capacities, no address drift

The product profile above is unnecessary if upward flows may depend on the
address. Let `C(v)` be the uniform reference capacity, so
`C(child)=A*C(v)`. Center the unequal down-flow fractions around their mean:

```text
qE = rE-rbar = -31/2^22,   qM = rM-rbar = 1/2^22,
2*qE + 62*qM = 0.
```

Define a signed edge debt `e(v)` from the root by `e(root)=0` and

```text
e(child_j(v)) = q_j*C(v) + e(v)/64.
```

Use these real-valued flows:

```text
down(v,j) = r_j*C(v) + e(v)/64
up(v)     = s*C(v) - e(v),       s = 255/2^24.
```

They satisfy both interior flow equations exactly. For the split at `v`, the
64 corrections to down-flow sum to `e(v)` and cancel its up-flow correction;
the base identity is `s+64*rbar=1-1/Q`. For the next occupancy at `v`, the
incoming edge contributes `+e(v)`, while its children contribute
`-sum_j e(child_j(v))=-e(v)`, since the `q_j` sum to zero. Thus the original
uniform reference-capacity recurrence is restored, without multiplying
capacities by address-dependent `pE`/`pM` factors.

For `E(v)=e(v)/C(v)`,

```text
E(child_j) = q_j/A + E(v)/(64*A).
```

The geometric bounds are exact:

```text
|E| <= 31/268,369,920       ~= 1.15513e-7
 E  <=  1/268,369,920       ~= 3.72621e-9.
```

The second, one-sided bound matters: end-address debt is negative. The signed
correction also changes the actual up-flow count to `pi=s*C-e`. Recomputing
the endpoint residuals gives `D_E-pi/2 = C/(2Q)+31e/64`, while each middle
interval contributes `D_M=-e/64`. Summing both sides for an interior child
gives residual `C/Q+e/64`; for an endpoint child the one-sided residual is
`C/(2Q)-31e/64`. The exact debt bounds give a worst endpoint reserve of
`8.57536e-8`, slightly larger than the interior reserve `5.96338e-8`.
Charging this larger reserve and the 69-wire rounding error still leaves
`2.54003e-8` in the exact arithmetic screen. Also `|E| < s`, so corrected
upward flows remain positive. These are arithmetic checks; the corresponding
address-sensitive stranger-count induction is still open.

More explicitly, for internal child `j` (`1 <= j <= 62`), the two
deterministic arguments of the positive parts in the per-side window estimate
are

```text
xL = C/(2Q) + (32-j)*e/64
xR = C/(2Q) + (j-31)*e/64.
```

Their positive-part sum is bounded by
`max(C/Q+E_positive*C/64, C/(2Q)+31*E_absolute*C/64)`; the endpoint-child
case has only one term and is covered by the second quantity. This is the
reserve calculation used by `sub1000_screen.py`.

The sorted-window algebra itself closes without a corrected half-fringe
hypothesis. For variable child widths `tau_j`, let `P_j = sum_{h<j} tau_h`.
If address slot `h` contains at most `tau_h + D_h` keys, the rank-window
injection gives

```text
wrong(j) <= max(0, O_L + sum_{h<j} D_h - pi/2)
          + max(0, O_R + sum_{h>j} D_h - pi/2).
```

Here `O_L,O_R` count parent outsiders below and above the full native
interval. This follows by bounding keys before each native cut from the left
and from the right, separately. Since both outsider counts are nonnegative,
`max(0,O+x) <= O+max(0,x)`; the sibling allowances on the two sides total
`63*rho`. Substituting the corrected endpoint and middle deficits gives the
`xL,xR` above, hence

```text
wrong(j) <= O_L + O_R + 63*rho + corrected_reserve*C.
```

Consequently, the old global condition
`pi/2 <= O_L + O_R + 63*rho` is unnecessary for this window estimate. This
closes the **real-valued two-tail algebra gate**. The generalized rank-window
lemma and per-slot accumulation compile in scratch file `VariableWindow.lean`;
the existing `window_real` theorem in `best` remains unchanged. The same file
proves the transfer from a subtree-mass identity and outsider bound to the
native-slot count. The remaining bulk obligation is to establish the outsider
invariant and aggregate wire-mass hypotheses for the corrected schedule.
This balanced flow removes the large product-profile/address mismatch at the
real-valued interior level. It does not yet handle integer rounding or the
root/top/bottom frontiers.

## What remains before formalization

The local vector and bounded-correction profile solve the interior
real-valued flow schedule. To get a network, the flow values must be converted
to integer bag sizes and even upward flows. The occupancy recurrence is

```text
next capacity of v = down-flow from parent(v) + sum(up-flows from children(v)).
```

Natural-number rounding errors must be controlled through the schedule,
including parity of `pi`; the root and bottom frontiers need their own flow
rules, and very small bags may need to stop splitting. The debt has rational
denominators that vary with path depth, so the `69`-wire bound must be proved
for the corrected schedule, including nonnegative splits and every ordinary
frontier case.

Next establish the outsider invariant and subtree-mass identity for the corrected schedule, then instantiate the proved per-slot transfer and two-tail lemmas. The corrected reserve and active rounding charge leave `2.54003e-8` in the conservative scalar screen. Then adapt the stage induction and terminal purity.
Only when those informal pieces close should this candidate be promoted to a
modular Lean prototype. The coefficient 945 is currently conditional on
those obligations.

### Variable-cut pack gate

The parent separator need not itself become ragged. `HasPackSemanticPropertyB2`
already controls every row cut of its rectangular pack. After that pack, the
parent's wires can be divided into variable rank intervals, and each child
can use a recursive network sized for its own interval. Thus the unequal
profile changes the tree of recursive pack sizes, not the dimensions of an
individual separator. This avoids the naive padding loss (the end/middle
target gap is about `1/2048`, much larger than `2^-21`).

The existing `window_real` proof identifies a sharper route than a generic
two-cut estimate. Its equal-width `BW.window_wrong_le` combines the left and
right rank tails using one global half-fringe condition; that is where the
term `63*Delta - pi/2` appears. For unequal child widths `tau_j`, keep the two
tails separate. If `D_j` bounds the excess of child `j`'s native-key count
over `tau_j`, and `O_L,O_R` are the parent outsiders below and above its native
rank interval, the same sorted-window argument gives the candidate bound

```text
wrong(j) <= max(0, O_L + sum_{h<j} D_h - pi/2)
          + max(0, O_R + sum_{h>j} D_h - pi/2).
```

For the proposed split, `tau_E = c/k - nu*c/(2*A*k)` at each end and
`tau_M=c/k` in the middle. Relative to equal native child intervals, the two
end deficits are

```text
D_E = nu*c/(2*A*k) = pi/2 + c/(2*Q),    D_M = 0.
```

Thus each side's endpoint deficit cancels its own `pi/2` term. The worst
remaining deterministic reserve is `c/Q`, plus the sibling and integer
rounding errors. The exact screen checks that even the crude all-siblings
bound leaves positive margin after charging `1/Q` and `69/2^34` per active
bag. This is the key conditional improvement over the global-tail estimate.

More explicitly, if every other child's native-key count is at most its
output width plus its local endpoint deficit and a common sibling allowance
`s`, then the per-side estimate gives, for every child `j`,

```text
wrong(j) <= parentOutsiders + 63*s + c/Q.
```

For an end child, only the opposite endpoint contributes the `c/(2Q)` reserve;
for a middle child, both endpoint reserves contribute, totaling `c/Q`. The
`63*s` term is bounded by the deliberately looser `64*s` used in the script.
This is the precise candidate replacement for the old
`63*Delta - pi/2` schedule-slack term; it still needs a theorem establishing
the stated native-key-count hypotheses under the path-dependent schedule.

### Discarded route: product profile plus the current address model

The product profile does **not** fit the current `KBag 64 d` native address
tree. In `Tree.lean`, every child interval has the same width `S`; in
`BadSendReal.window_real`, all 64 cuts are consequently at `Ulo + j*S`.
But the flow profile assigns end and middle children different capacities,
with exact normalized factors

```text
pE = 65504/65535,   pM = 65536/65535.
```

Keeping the equal `KBag` intervals while multiplying capacities by these
factors creates an exponentially growing address/capacity discrepancy along
an extreme path: `pE^35 = 0.9835764...`, while `pM^35 = 1.0005342...`.
At a reference capacity of `2^36`, an all-end path is short by about
`1.13e9` wires relative to the equal native interval. The screened allowance
is on the order of `1e-7` of the active capacity. Thus the existing `hM`
hypothesis cannot simply be reused with the product-profile capacities.

The one-level normalization itself exposes the issue. The physical target
down-flow fractions have average
`rbar = 65535/2^22`; normalizing them so 64 native child intervals exactly
partition a full parent interval gives widths `p_j/64` of that parent. These
are larger than the proposed physical fractions `r_j` by the common relative
factor `1/(1 - 2^-16)`. That discrepancy is the mass reserved for upward
flow. A valid variable address tree must explicitly represent this reserved
mass (or choose a different cut convention) while retaining the two-sided
endpoint cancellation. Merely replacing equal cuts by widths proportional
to `p_j` does not establish the needed `D_j` bounds.

This rules out combining the product profile with the existing address tree
without more work. The bounded signed correction above is the current route
because it restores uniform reference capacities. A reserve-aware variable
address partition remains a fallback if the correction does not survive the
native-key-count proof.

That capacity-versus-address mismatch belongs only to the discarded product
profile. The bounded signed correction keeps the reference capacity uniform,
and its zero-sum debt recurrence preserves level-uniform occupancy. Therefore
the existing Lemma 4.1 native-slot estimate can be reused if the corrected
schedule establishes the same outsider invariant and aggregate wire-mass
identity. The scratch transfer lemma records the exact subtree-mass and
outsider premises needed. Charging all 64 sibling contributions instead of
subtracting the distinguished branch still leaves positive scalar margin after
the two-tail reserve and active rounding charge, as checked by
`sub1000_screen.py`; this does not prove the outsider induction.

The sorted-window part of the decision gate is closed in scratch. The remaining bulk gate is to establish the corrected schedule's outsider invariant and local subtree-mass identity, then its integer row-rounding rule. If those fit the screened budget, handle adaptive small-bag termination and root/frontier cases. The candidate remains conditional until these are connected to a complete sorting network.
