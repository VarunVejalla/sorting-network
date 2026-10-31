# Equalized ragged geometry across D2 senders

2026-10-22. Exact finite screen; no provider or sorting theorem claimed.

For a sender with `a=2F+64B`, where `F=up/2` and `B=(a-up)/64`, use

```text
n = max(16, ceil(B/127), ceil(a/8192)).
b_j in {floor(B/n), ceil(B/n)}, with sum b_j=B.
f_j = floor((floor(a/n)-64*b_j)/2),
then add one to exactly enough columns so sum f_j=F.
```

This aligns fringe width with bulk height so the columns have nearly equal
total height. `ragged_all_senders.py` checks the construction on every
distinct positive-up ordinary sender pair in the compressed D2 flow through
depth100 at scale8192: 19,606 distinct pairs admit `f_j>=13` and
`2*f_j+64*b_j<=8192`. The all-depth lower-fringe inequality and startup cases
remain to be proved.

For mask extraction, pad with dummy keys smaller than every live key. An
ascending column sort then moves the live keys to a deterministic suffix;
these dummies correspond to Boolean zero in the threshold argument.

The maximum cumulative-cut symmetric difference from a common row cut in
that depth100 scan is `16n` cells, attained by equal multiplicities of
`(f,b)=(256,120)` and `(224,121)`. Under the old B2 parameters, the common-cut
transfer allowance was too small. A relaxed parameter pair fits the observed
geometric charge:

There is a profile-independent median-cut argument conditional on this
equalized construction. Write `b_j=q+β_j` and
`2*f_j+64*b_j=L+2*e_j`, where `β_j,e_j∈{0,1}` and `L` is the largest even
integer not exceeding `floor(a/n)`. The boundary after `s` bulk groups is

```text
R_j(s) = 8192 - L/2 - (32-s)q - (32-s)β_j - e_j.
```

The sum of absolute deviations of `β_j` from its mean is at most `n/2`, as
is the corresponding sum for `e_j`. Hence the total deviation of boundaries
from their mean is at most `(|32-s|+1)n/2 ≤ 33n/2`. An integer median boundary
minimizes the sum of absolute deviations, so each cumulative ragged cut
differs from one uniform row cut by at most `33n/2` cells. The relaxed B2
transfer allowance is `16.7936n`, strictly above `16.5n`.

The varying fringes can also use one uniform F2 parameter per sender. Let
`f_* = min_j f_j`. In each column the ragged bulk occupies a subset of the
uniform region above the last `f_*` rows, because `f_j>=f_*`. Thus F2 at
width `f_*` bounds rank leakage into every ragged bulk port, with no extra
mask-mismatch charge; apply the flipped F2 property for the other
orientation. The depth30 screen has `f_*=14` as its minimum, and its smallest
column counts by fringe minimum are `n=8195` for14, `4157` for15, and `4096`
for16. `fringe_cert_v2.py` passes the shifted-cut closed screen at
`(g1,g2,c,b,J)=(7,9,1/3,6/5,1)`, `delta*f_*n=18`, for `(14,8195)` with
failure budget `1/1000`; `(15,4157)` and `(16,4096)` pass with budget `1/10`.
Those budgets may fit the local existence union for this sender geometry,
alongside the round-one and B2 events; no union over repeated sender
occurrences is needed if a separate universal core is selected for each
geometry. The combined probabilities and all-depth parameter family have
not been proved. The generic Lean F2 guard `delta*f*16>=1` fails at
these large column counts; a local-dimension version is still needed.

```text
d = 11/2500,       full B2 leakage d/2 = 11/5000 = 0.0022 mn
epsB = 17/2000,    local cut budget epsB/2 = 0.00425 mn
geometry charge   (33/2)n = (33/16384) mn = 0.00201416015625 mn
combined bound    0.00421416015625 mn < 0.00425 mn.
```

At `m=8192`, `E1=371/10^8`, `lambda=1`, the round-two exponent is
`m*(d/2-(13/18)*E1) ~= 18.0`, against `log(2*(m+1)) ~= 9.704`; for `n=16`
the rough log failure-fraction screen is `-132.7`. This only checks the
round-two exponent. Round one, the F2 probability family, fixed-mask
extraction, a proof that the chosen integer profile always has `f_j>=14`,
and the global rank recurrence
remain open.
The relaxed local `epsB` must pass that recurrence before it can support the
nominal273 coefficient.

## Corrected 13-row waterfill gate

`ragged_all_senders.py --allocation waterfill` chooses the same minimal column
count `n`, distributes `B` balanced bulk widths, and water-fills total heights
`x_j=f_j+32*b_j` subject to `13+32*b_j <= x_j <= 4096` and
`sum x_j=a/2`. Thus every column has `f_j>=13` whenever `F=pi/2 >=13n`.
The weaker floor is deliberate: the corrected sender factor is `279/256`, so
the earlier `14n` derivation from `271/256` was not justified.

The exact depth-100 screen passes with `--tail 13`: all 19,606 distinct
positive-up sender pairs fit, the smallest observed fringe remains14, and the
largest observed median-cut mismatch remains16 cells per column, below the
`16.7936n` transfer allowance. At the minimum-fringe witness the profile has
three types, including 75 columns of type `(47,126)` among the many
`(14,127)` and `(15,127)` columns. This is finite evidence, not an all-depth
profile theorem.

There is a conditional all-depth proof of `F>=13n` from the corrected
`a/c<=279/256` sender lemma and the role-specific capacity floors. For
`mid`/`botDesc`, `pi/c=15/4096`, so `a/pi<=279*16/15=1488/5`; for
`topRise`, `pi/c=1/256`, so `a/pi<=279`. Hence uniformly

```text
F/a >= 5/2976,                 F/B >= 160/1483.
```

The schedule gives `c>=2^26` for `mid`/`botDesc` and `c>=2^25` for
`topRise`, hence `F>=65536` for every ordinary positive-up sender. With
`n=max(16,ceil(B/127),ceil(a/8192))`, this handles `n<=19`. If
`n=ceil(a/8192)>=20`, then `F>(1280/93)(n-1)>=13n`. If
`n=ceil(B/127)>=20`, then `F>(20320/1483)(n-1)>=13n`. Thus waterfill's
13-row feasible region follows conditionally from the corrected factor and
schedule floors; no 14-row claim is needed.

A generic capacity floor and sender factor alone do not control waterfill's
cut mismatch. For example, `a=813440`, `pi=3840` gives `c=2^20` under the
`mid`/`botDesc` quota ratio, `a/c<279/256`, `F=1920`, `B=12650`, and `n=100`.
Its waterfill profile is
`30*(24,126) + 20*(25,126) + 50*(14,127)`, with mismatch `26.8n`; this is
not an actual scheduled D2 state. The stronger role-specific capacity floors
are needed for the all-depth geometric argument.

The waterfill median-cut bound follows conditionally on the `279/256` sender
lemma. For `(3,3,2)`, `log2(c)=3d+3i-2t+9`; the activity inequalities give
`c>=2^26` at `mid`/`botDesc` and `c>=2^25` at `topRise`. Therefore
`F>=65536`.

Write `B=qn+r`, `0<=r<n`. If waterfill does not pin the `b=q+1` columns at
their lower height `13+32(q+1)`, all heights `x_j=f_j+32b_j` differ by at
most one. The median-cut formula is
`R_j(s)=8192-x_j-(32-s)b_j`; since both `x_j` and `b_j` then have L1
deviation at most `n/2`, each cut mismatch is at most `33n/2`.

If those higher-bulk columns are pinned, then
`F/n+32(r/n)<45`, so `n>65536/45>1456`. The count `n` cannot then be set by
`ceil(a/8192)`: in that case `a>8192(n-1)` and the pinned inequality imply
`32q>4051-4096/n`; but `q<=126` (otherwise `r=0` and there is no pin), which
forces `n<4096/19<216`, a contradiction. Thus `n=ceil(B/127)`, so
`B>127(n-1)`. As `n>1456`, this forces `q=126` and fewer than127 columns
with `b=126`; the `b=127` group is the median group. Across all 65 cuts, a
`b=126` column's boundary differs from that median by at most64, so the total
mismatch is less than `64*127=8128`, below `16.7936n` for `n>1456`.

This closes the all-depth geometric mismatch estimate conditionally on the
corrected sender-factor identity and schedule proof. Provider probabilities,
the global rank recurrence, root initialization, and terminal sorting remain
separate open gates.

### 13-row F2 threshold screen

An additional rational-tangent screen lowers the closed certificate threshold
for the support-cap-18 family at `n=8307` to nine rows. With
`f=9`, `delta=18/(9*8307)`, `J=1`, and
`(g1,g2,c,b)=(2,4,2/5,1)`, the exact interval checks give
`ln(2P1)<=-7.50129`, `ln(2P2)<=-13.4767`; the closed sums give
`ln(2P1)<=-7.50129`, `ln(2P2)<=-7.67752`, both below `ln(1/1000)`.
Concavity brackets the R1b maximizer in `[1527/10000,1528/10000]`, with
positive derivative at the left endpoint and negative derivative at the
right. This remains conditional on replacing the generic `hf16` guard by the
local-dimension condition `delta*f*n=18`; it is a probability screen, not a
sender-family provider. Reproduce the check with
`python upper-bound/experiments/prefix-flux/ragged_provider_probability_screen.py`.

At the candidate minimum dimension `n=3832`, the F2 interval screen with
`f=13`, `delta=18/(13n)`, `J=3`, `(g1,g2,c,b)=(3,7,2/5,2)` passes the exact
per-E certificate for both orientations: `ln(2P1)<=-16.8139` and
`ln(2P2)<=-15.5087`, against the `1/1000` budgets. Here `J=1/eps_F`, so this
is `eps_F=1/3`. The generic closed R1 sum was too loose
(`ln(2P1)<=-4.80757`), but a rationally bracketed concavity estimate now
closes it. For
`psi(s)=s ln(eJ/(sD))+(Delta*s+b)ln(eDs/(Delta*s+b))`, with
`D=delta*f=18/3832` and `Delta=4`, interval evaluation verifies
`psi'(927/10000)>0` and `psi'(928/10000)<0`. Concavity puts the maximizer in
that interval; the tangent at its left endpoint gives
`psi*<=psi(927/10000)+psi'(927/10000)/10000 < -17.1117`, hence
`lambda_b>9.5117`. The resulting closed sums pass both orientations at
`1/1000`. This bracket is currently checked by `mpmath.iv`; its rational-log
inequalities still need a Lean certificate. A weaker point `J=2`,
`(c,b)=(1/4,2)`, passes both exact and closed
screens but only gives `eps_F=1/2`. In both cases the global Lean guard
`delta*f*16>=1` fails; the intended local condition is `delta*f*n=18`.

This makes the 13-row probability gate numerically plausible, conditional on
proving the all-depth sender dimension floor `n>=3832`. Fix
`delta=18/(13*3832)` once for all such senders: the certificate depends on
`delta*f=18/3832` and is uniform in column count above its stated rank-cap
threshold, while `delta*f*n>=18` for every `n>=3832`. It does not show that
`eps_F=1/3` is small enough for the global rank recurrence, nor establish the
common-mask provider.

### Larger support-cap screen

At the same minimum dimension `n=3832`, retaining `f=13`, `(g1,g2)=(3,7)`,
`(c,b)=(2/5,2)`, `J=3`, and failure budget `1/1000`, I increased
`delta*f*n` from18 to48. The interval-evaluated per-`E` certificate still
passes both orientations: the verbose screen gives
`ln(2P1)<=-12.821` and `ln(2P2)<=-11.227`. Thus the sampled F2 contract can
cover support cap48 at this geometry, rather than18. The current
Lean-friendly closed envelope fails at these parameters (and the local
replacement for `hf16` is still needed), so this is a numerical lead, not a
provider theorem. Reproduce through the added `delta*f*n=48` case in
`ragged_provider_probability_screen.py`.

There is a concrete conditional route to that dimension floor. For an
ordinary sender at `t>=3`, the lower half of the two-step identity gives
`a/c>=479/512` when the child roles are mid/botDesc, and at least that much
when they are botRise. Together with the role floor `c>=2^25`, this gives
`ceil(a/8192)>=3832`. The only schedule exception is the inactive-child case:
it is a botDesc at `t=3i-4`, with `i=omega(t)`, so the physical capacity
formula is `log2(c)=3(d-i)+17`. Since it is processed before `tf(d)`, the
schedule gives `d-i>=4`, hence `c>=2^29`; the same cut identity gives
`a/c>=31/512`: at its `botRise` predecessor, send-all means
`g_old+rho_old=(G_old+a_old)/c_old=native/c_old=1/256` (the quota `rho_old`
alone need not equal `1/256`), and the current deficit is at most `1/512`.
Thus `ceil(a/8192)>=3968`. Startup senders satisfy
`a/8192=8^(d-1)` at `t=1` and
`a/8192>= (63/64)8^(d-2)` at `t=2`; both exceed3832 for `d>=6`.
This would prove `n>=3832` for all ordinary positive-up senders at every
depth `d>=6`, provided the all-depth noncrossing induction and the stated
schedule/startup identities are completed. Depths below6 are finitely many
exceptions and do not affect the limsup family.

Reproduce with:

```text
python ragged_all_senders.py --depth 100 --scale 8192 --min-columns 16 --min-time 3 --allocation waterfill --tail 13
```

Verification run:

```text
python upper-bound/experiments/prefix-flux/ragged_all_senders.py --depth 100 --scale 8192 --min-columns 16 --min-time 3 --allocation waterfill --tail 13
```

For the waterfill run with `--allocation waterfill --tail 13`, the result is
204,348 active ordinary sender rows, 19,606 distinct `(a,up)` pairs, no
geometric shape failures, minimum fringe14, and maximum mismatch16 cells per
column. These are finite checks, not an all-depth proof.
