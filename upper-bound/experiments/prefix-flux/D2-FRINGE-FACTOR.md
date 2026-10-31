# A rational all-depth fringe-factor target for `(3,3,2)`

2026-10-21. Paper invariant proposal; finite-flow evidence only. No local
provider or sorting bound is claimed.

## Why `9/8` is the useful target

Use D2 parameters `k=8`, `A=8`, `nu=1/4`, scale `m=8192` (row height
`2^13`). For an active sender let `a` be its exact integer allocation,
`pi` its up-port size, and

```text
c = scale * Par.cap(d, level, t).
```

The equivalent full-row fringe width is `m*pi/(2a)` when the exact rectangle
equations `a=m*n` and `pi=2*f*n` hold. This ratio is only a geometry screen;
the finite flow scan does not establish those divisibility/shape equations.
Under that caveat, the D2 formulas give:

| Role | `pi/c` | Equivalent fringe rows |
|---|---:|---:|
| `mid`, `botDesc` | `15/4096` | `15 / (a/c)` |
| `topRise` | `1/256` | `16 / (a/c)` |
| `botRise` | `a/c` | `4096` |
| `topDesc` | `0` | no positive fringe |

For positive-up senders in the ordinary `mid`, `botDesc`, and `topRise`
roles, therefore the single bound

```text
a / c <= 9/8
```

gives at least `40/3` equivalent rows for
`mid`/`botDesc`, and at least `128/9` rows for `topRise`. Both exceed the
13-row geometric threshold of the proposed local tail interface. `botRise`
also passes directly: its up-port has size `a`, so it gives 4096 equivalent
rows. `topDesc` has positive allocations but `pi=0` (including at later
stages), so this fringe calculation does not apply; its separate obligation
is to preserve the required tail/rank contract without an up-fringe. The
all-depth sender theorem also needs a schedule lemma excluding active leaf
senders or a dedicated leaf case.
This rational slack avoids proving the exact observed minimum `8192/559`.

## Exact normalized recurrence to attack

The flow identity is `a = sum_child G_child - G_parent`, where `G` is the
subtree deficit. Since the capacity ratio from a parent level to one child
level is exactly `A=8`, normalized deficits

```text
g(node,t) = G(node,t) / (scale * Par.cap(d, level, t))
```

give the exact sender relation

```text
a/c = 8 * sum_child g(child,t) - g(parent,t).
```

At the same time `t`, child capacity is 8 times parent capacity, yielding
the displayed identity. For updates to time `t+1`, the child capacity is
instead twice the current parent capacity. Thus translating the D2 exact
updates into normalized next-state inequalities requires tracking this
different factor. The child multiplicities/types are one same-side end, one
other-side end, and six interior children. Candidate updates are
`theta_same = pi/2 + G_parent`, `theta_other = pi/2`, and
`theta_interior = 0`, with schedule top/bottom special cases; a proof must
also show the exact interval cuts do not saturate or cross the relevant end
child. A role/type invariant for ordinary positive-up senders must imply
`a/c <= 9/8`. The uniform Chvatal allocation formula is not valid for this
flow.

Writing `rho = pi/(scale*c)` for the sender's current normalized up-port and
`g_parent = G_parent/(scale*c)`, the ordinary update translates exactly to

```text
g_same(child,t+1)  = g_parent/2 + rho/4
g_other(child,t+1) = rho/4
g_interior(child,t+1) = 0.
```

These factors use `cap(child,t+1)=2*cap(parent,t)`. This is the concrete
finite-dimensional transition to close under a role/type invariant; it does
not apply to `botRise`, whose update has no `theta` split, or `topDesc`, whose
up-port is zero.

## Two-step allocation identity and a sufficient invariant

There is a direct identity for an ordinary active sender `x=(i,t)` if `x`
also had an ordinary update at `t-2`. Write `rho_x(u)=pi_x(u)/(scale*cap(i,u))`
and `g_x(u)=G_x(u)/(scale*cap(i,u))`. Let `y` range over its eight children,
with multiplicity, and set `rho_y(t-1)=0` when that child is inactive. The
parent's update at `t-2` sets each child's deficit to its `theta`; at `t-1`
each active child increases its own deficit by `pi_y`; the parent updates
again at `t`. Using `cap(i,t)=cap(i,t-2)/16` and
`cap(i+1,t-1)=32*cap(i,t)`, the exact conservation equation becomes

```text
a_x(t)/c_x(t) = 16*g_x(t-2) + 16*rho_x(t-2)
                + 32*sum_children rho_y(t-1) - g_x(t).
```

Here the `16*g + 16*rho` term is the sum of the two end-child `theta`
contributions; the six interior `theta`s are zero. This identity was checked
on 2,646 matching ordinary transitions in the typed D2 simulator. A direct
audit against the compressed standard `(3,3,2)` `FlowDAG` is now available as
`d2_factor_identity_audit.py`; it checks the identity and role split in the
actual integer-cut recurrence.

It yields a particularly simple sufficient invariant. If, on these
transitions, `g_x(t-2) <= 1/256`, `rho_x(t-2) <= 1/256`, and each child
`rho_y(t-1) <= 1/256`, then nonnegativity of `g_x(t)` gives

```text
a_x(t)/c_x(t) <= 16/256 + 16/256 + 32*8/256 = 9/8.
```

The same identity gives a strict lower margin for cut noncrossing, which was
not explicit in the earlier upper-bound discussion. Write `rho_x(t)` for the
current port ratio. If the predecessor at `t-2` is ordinary, then
`g_x(t-2)>=0`, `rho_x(t-2)>=15/4096`, the child-port sum is nonnegative,
`g_x(t)<=1/512`, and `rho_x(t)<=1/256` imply

```text
(a_x(t)-pi_x(t))/c_x(t) >= 16*(15/4096) - 1/512 - 1/256 = 27/512.
```

If that predecessor is `botRise`, its unchanged-child identity gives
`g_x(t-2)+rho_x(t-2)=1/256` and the intermediate child-port sum is zero.
Then

```text
(a_x(t)-pi_x(t))/c_x(t) >= 16/256 - 1/512 - 1/256 = 29/512.
```

Both cases establish `pi<=a` with room, before applying the current cut. The
eight-child ordinary update identity and these arithmetic implications are
kernel-checked in `D2ScheduleReserve.lean` as a standalone rational model. The
capacity ratios `cap(i,t-2)=16 cap(i,t)` and
`cap(i+1,t-1)=32 cap(i,t)` are also proved there from the `(8,8,1/4)`
capacity formula. Matching that model to the actual `FlowDAG`/Lean recurrence
and proving its all-role port bounds on reachable states remain open.

The depth30 typed scan sees `max rho = 1/256` and `max g =
983033/536870912 < 1/256`, so these are plausible exact invariant bounds,
not just a numerical fit. The all-depth fringe argument reduces to proving
the `g` induction and the explicit schedule cases below. For a `topDesc`
predecessor, the parent sets both end deficits to zero, so the same identity
has no `16*g+16*rho` term; that case is covered by the child-rho bound alone.

The special cases have a compact prospective treatment. For these parameters
and `t>=3`, `botRise` occurs at `t=3j`, `i=omega(t)=j+2`. Therefore

```text
scale*native(i) / (scale * cap(i,t))
  = native(i) / cap(i,t) = 2^(4 + 2t - 6i) = 1/256,
```

and the capacity bound `a<=scale*native(i)` proves `rho<=1/256` for every
`botRise` sender. If an ordinary sender's previous active time `t-2` was a
`botRise`, then `t=3j+2`, `i=j+2`, so the same capacity argument gives
`a/c<=native/cap=1/16` at the current time. When an ordinary sender has no
active sender at `t-2`, the only positive-up startup case in the schedule is
`(t,i)=(2,2)`, also with `native/cap=1/16`; `t=1` is the explicit `topRise`
case. A previous `topDesc` update sets all child deficits to zero, giving
`a/c = 32*sum_children rho_child - g_current <= 1`.

## Paper proof candidate for the all-depth schedule cases

For `t>=2` and levels `0<=i<=d`, the explicit schedule can be rewritten
(for `t<=tf(d)`) as

```text
i is active at (d,t) iff i ≡ t (mod 2),
  3*i >= 2*t - 3*d + 11, and 3*i < t + 8.
```

At `t=1`, the explicit schedule has only level `i=1` active. The cutoff
`t<=tf(d)` is essential; the inequalities alone also admit levels after the
schedule has terminated.

This form proves the one-step parent closure needed for the deficit induction.
Let `x=(i,t)` be an ordinary positive-up sender with `2<=t<tf`. Its parent
`p=(i-1,t-1)` has the required parity. The child's upper inequality implies
the parent's upper inequality. The parent's lower inequality follows from
the child's lower inequality except possibly when
`3*i = 2*t - 3*d + 11`; equality can occur only for `t ≡ 2 (mod 3)`. In
that case `i=alpha(t)` and the next lower endpoint is `alpha(t+1)=i+1`, so
`x` is `topDesc`, contrary to positive up-port. Thus `p` is active. It cannot
be `botRise`, since then `omega(t)<omega(t-1)=i-1`, making child level `i`
inactive at time `t`. Hence `p` is either ordinary or `topDesc`.

Induct on stage `t` for the stronger `g_x(t)<=1/512` at ordinary senders.
The root's initial update sets its children to zero. A `topDesc` parent also
sets the child deficit to zero. An ordinary parent gives
`g_child <= g_parent/2 + rho_parent/4 <= 1/1024 + 1/1024 = 1/512`, using
the exact capacity ratio `cap(child,t)/cap(parent,t-1)=2` and the role bound
`rho_parent<=1/256`. This is the bound needed both for the two-step identity
and the endpoint-reserve argument below.

For an ordinary sender `x=(i,t)` with `t>=3`, it is also active at `t-2`.
At `t=3`, the only ordinary positive-up sender is level `i=1`; level `i=3`,
when active, is botRise because `omega(3)=3` and `omega(4)=2`. The explicit
`t=1` schedule has `i=1` active. For `t>=4`, the lower activity inequality
at `t-2` follows from the one at `t`; if the upper inequality there failed,
parity and `3*i<t+8` force `3*i=t+6`. This is exactly the case
`i=omega(t)` with `omega(t+1)=i-1`, namely `botRise`, which ordinary senders
exclude. If `x` was ordinary at `t-2`, use the
two-step identity and the proved `g,rho` bounds. If it was `topDesc`, its
update sets all child theta terms to zero, leaving
`a/c=32*sum_children rho_child-g_x(t)<=1`. If it was `botRise`, then
`t-2=3j`, `i=j+2`, and `native/cap=1/16`, so `a/c<=1/16` directly. The
remaining startup sender `(t,i)=(2,2)` has the same native/cap bound; `t=1`
has `a/c=1` from the root's exact first split. Thus the all-depth ordinary
sender conclusion is `a/c<=9/8`, provided the stated schedule algebra and
the exact two-step conservation identity match the full D2 definition.

There are no active leaves in processed stages. If `i=d` were active for
`t<tf`, the activity inequalities and parity force `t=3d-6`. For `d>=4`,
at `t-2=3d-8` the formulas give `alpha=d` and `omega=d-2`, hence
`tf<=3d-8<t`; for `d=3`, the explicit schedule gives `tf=2<3`. Therefore
the eight-child identity covers every ordinary sender to which it is applied.
This is a paper derivation, not yet checked against all Lean endpoint
conventions. A fresh mathematical review checked the cutoff, parity,
`topDesc`, `botRise`, and leaf cases and found no remaining error in this
schedule argument. The D2 conservation identities and a compatible provider
still need independent formal statements before Lean transfer.

This schedule statement must be restricted to those ordinary-sender states;
it is false for arbitrary active nodes. A finite counterexample to the broader
claim is an active topDesc node at `(d,t,i)=(10,11,1)` whose parent `(0,10)`
is inactive. The exact audit script checks these cases and the rational flow
inequalities:

```text
python upper-bound/experiments/prefix-flux/d2_fringe_audit.py --depth 100
```

Through depth 100 it checks 117,962 ordinary positive-up schedule states,
including the explicit startup cases, and sees no violation after those
exceptions. It also checks the activity formula and no-leaf assertion at all
processed stages in that finite range. The exact scaled FlowDAG scan checks
217,470 active rows; all
ordinary rows satisfy `g<=1/256`, `rho<=1/256`, and `a/c<=9/8`. The largest
ordinary `a/c` is `8385/8192`, and the largest ordinary `g` is
`276701161105643274233/151115727451828646838272 < 1/256`. These are finite
checks only. The all-depth proof still needs floor/parity schedule lemmas; the
provider, global profile transfer, root, and terminal sorting gates remain
open.

## Finite evidence and limits

## Corrected role-split target `a/c <= 279/256`

The earlier `271/256` case split incorrectly set the old `botDesc` deficit to
zero. The exact flow has positive `g` at some `botDesc` states, so that sharper
bound is not established by that argument. Using the proved-in-target
invariant `g<=1/512` at all ordinary positive-up roles instead gives the
slightly weaker `279/256` target, still strong enough for at least13 fringe
rows in the 8192-row core.

For an ordinary sender `x=(i,t)`, `t>=3`, the child role at `(i+1,t-1)` is
not `topRise`. If it is `botRise`, the schedule forces current and preceding
sender roles both to be `botDesc`; the two-step identity gives
`16*g_old + 15/256 + 1 - g_current <= 16/512 +15/256+1 =279/256`.
Here `1` is the eight same-role children term `32*8*(1/256)`.

Otherwise all active children are `mid`/`botDesc`, so their total term is at
most `15/16`; inactive children contribute zero. A `mid` predecessor gives
`16/512+15/256+15/16=263/256`; a `botDesc` predecessor gives at most
`16/512+15/256+15/16=263/256`; a `topRise` predecessor gives at most
`16/512+16/256+15/16=264/256`. A `topDesc` predecessor has `g=pi=0`, so
its child term is at most1. A `botRise` predecessor and the startup cases
have the direct native-capacity bound `a/c<=1/16`. Thus every case is below
`9/8`, with maximum target `279/256`, assuming the schedule exclusions,
boundary fact for `topDesc`, and exact identity.

### Closing the noncrossing induction

The two-step estimate can also supply the lower bound needed to justify each
ordinary cut, rather than assuming valid cuts in advance. Induct over stages,
maintaining the one-step bound `g<=1/512` at ordinary positive-up states.
To establish an ordinary sender's cut at stage `t>=3`, apply the same exact
identity and the schedule partition for its children at `(i+1,t-1)`:

- If those children have role `mid` or `botDesc`, their combined term is
  `32*8*(15/4096)=15/16`. The nonnegative old terms and
  `g_current<=1/512` give `a/c>=479/512>1/256`.
- If they have role `botRise`, their combined term is1, giving
  `a/c>=511/512>1/256`.
- If they are inactive, the schedule forces the sender at `(i,t-2)` to be
  `botRise`. Here the useful invariant is not `rho_old=1/256` (which is
  false), but the exact sum `g_old+rho_old=1/256`. To justify it, write the
  `botRise` time as `t-2=3j`, so its level is `i=j+2`. The explicit boundary
  formula gives `omega(3q)=q+2`, `omega(3q+1)=q+1`, and
  `omega(3q+2)=q+2`; consequently `omega(s)<=j+1=i-1` for every
  `s<=3j-1`. Thus the sender at level `i` itself had no earlier update that
  could cut its children. At `3j` it is `botRise`, which leaves those child
  deficits unchanged, and at `3j+1` it is inactive because
  `omega(3j+1)=j+1<i`. The eight children therefore retain their full native
  deficits through `t-1`; their deficits sum to
  `8*native(i+1)=native(i)`. By the allocation definition,
  `G_old+a_old` is this sum; send-all gives `pi_old=a_old`, and the schedule
  capacity formula gives `c_old=256*native(i)`. Thus the identity gives
  `a/c=16(g_old+rho_old)-g_current >= 16/256-1/512=31/512`, which is
  greater than the current quota ratio `rho_current<=1/256`.

The schedule excludes `topDesc` and `topRise` children in these ordinary
sender states. Since each current ordinary quota satisfies `rho<=1/256`,
these estimates prove `a>=pi` and hence that its two cut fronts do not cross.
The base/startup stages are direct. This closes the validity/factor circularity
provided the schedule case lemmas, the exact identity, and the one-step deficit
update are proved for all depths. `d2_fringe_audit.py` checks this child-role
partition (including inactive-child predecessor `botRise`) on finite
schedules.

### Separate end-child containment obligation

The preceding argument establishes only that the two global cut fronts do
not cross (`a>=pi`). To use the unsaturated endpoint updates, one must also
show that each front fits in its own end child. In the exact integer
recurrence these are the independent inequalities

```text
U_first >= low + pi/2
U_last  >= high + pi/2,
```

where `U_first` and `U_last` are the pre-update deficits of the endpoint
children (and `pi` is even in ordinary updates). The simulator clamps each
cut to the child capacity, so noncrossing alone does not imply either bound;
without them the proposed `theta_same`/`theta_other` formulas cannot yet be
used inductively.

An exact scan of the compressed standard `(3,3,2)` flow through depth100
found no endpoint containment failure among 204,348 distinct ordinary
positive-up DAG states. The minimum normalized endpoint slack
`(U_first - low - pi/2)/cap(child,t)` by role was `63/4096` for `topRise`,
`80280230208783968632839/154742504910672534362390528` for `botDesc`
(`0.000518798828125`), and `1185/65536` for `mid`; left and right agree by
symmetry. This is finite evidence, not an all-depth invariant. The next
paper gate is to prove these endpoint inequalities from a strengthened
role-sensitive state invariant (or find a counterexample); the `g` and
two-step inductions above remain conditional until that gate closes.
The reproducible exact check is included in
`d2_factor_identity_audit.py --depth 100 --row-bits 13`; it checks endpoint
containment across all active ordinary shared states, including startup,
separately from the two-step identity scan.

### Candidate reserve invariant for closing containment

The finite data suggest a much simpler sufficient invariant than the measured
positive slack: for every ordinary positive-up sender, each endpoint child
has reserve at least `c/128`, where `c=scale*cap(d,i,t)` is the sender's
current capacity. Together with `G<=c/512` and `pi<=c/256`, this gives
`low+pi/2 <= G+pi/2 <= c/256 < c/128`, and symmetrically at the right end.
The exact scan's minimum reserve by current role is `1/8` (`topRise`), `1/128`
(`botDesc`), and `75/512` (`mid`).

Here is a candidate induction for the reserve bound. Except for startup,
schedule arithmetic gives an ordinary positive-up sender `(i,t)` an active
predecessor `(i,t-2)`, whose role is ordinary or `botRise`. The `topDesc`
predecessor is excluded by monotonicity of `alpha` on each parity class (the
parity-rounded `alpha` is not globally nondecreasing). A `topDesc` at `t-2`
has `i=alpha(t-2)<alpha(t-1)`. Since `t` and `t-2` have the same parity,
`alpha(t)>=alpha(t-2)=i`; current activity gives `alpha(t)<=i`, so
`alpha(t)=i`. Since `t+1` and `t-1` also have the same parity,
`alpha(t+1)>=alpha(t-1)>i`, making the current node `topDesc`, contrary to
ordinary positive-up status. If the predecessor is ordinary, its already-justified
unsaturated cut leaves each endpoint child deficit at least `pi_old/2`:
the endpoint cut itself is `low_old+pi_old/2` or
`high_old+pi_old/2`, and the opposite cut can only add to that child's
deficit. At the intervening stage `t-1`, the same-node sender is inactive;
the child can only increase its own deficit, so this reserve cannot decrease.
The predecessor quota ratio is either `1/256` (`topRise`) or `15/4096`
(`mid`/`botDesc`), and
`cap(d,i,t-2)=16*cap(d,i,t)`, so the reserve is at least
`15*c/512 > c/128`. If the predecessor is `botRise`, its children are
unchanged. Writing `t-2=3j`, `i=j+2`, the schedule residues give
`omega(s)<=j+1=i-1` for all `s<=3j-1`; hence level `i` itself was inactive
before the `botRise`. Also `omega(3j)=i` and `omega(3j+1)=i-1`, so level `i`
does not cut its children at either of those times. The children remain
native through `t-1`, exactly `c/128`. At startup, `t=1` has native
level-2 endpoints with reserve `c/8`, and `(t,i)=(2,2)` has native level-3
endpoints with reserve `c/128` directly.

This would close the cut circularity by simultaneous induction over stages:
the inherited `G<=c/512` bound follows from the already-valid parent update
at `t-1`; the reserve follows from the already-valid same-node update at
`t-2` or from the inactive `botRise` case; the two inequalities then prove
both endpoint cuts fit; finally the two-step allocation estimate proves
noncrossing before applying the current update. This is a paper candidate,
not yet a theorem: its all-depth schedule partition, startup constants, and
translation of the previous endpoint cuts into current child deficits need
an independent check. The audit now also reports the finite reserve and
front ratios by role to make counterexamples or corrections easy to locate.

The earlier wording that the old `botRise` quota alone equals `1/256` was
incorrect; it is the sum `g_old+rho_old` that equals `1/256`, and this repairs
the inactive-child case without an additional allocation-floor assumption.
The topDesc boundary fact `g=0` is also needed for the predecessor case. It follows
if the active topDesc update is shown to have zero parent deficit and zero
quota, as required by its all-zero child update; this still needs a clean
all-depth statement. The two-step identity also extends to a `botRise`
predecessor: it has `pi=a`, leaves child deficits unchanged, and their sum is
`G+a`.

The corresponding exact finite audit is
`d2_fringe_audit.py --depth 100 --scale 8192 --shape-depth 30`: it checked
the proposed `g<=1/512` and `a/c<=279/256` assertions on the compressed flow.
The observed largest ordinary ratio was `8385/8192`; the larger rational cap
is needed for a simple uniform proof, not because the scan approaches it.
Together with `ragged_all_senders.py --depth 100 --scale 8192
--min-columns 16 --min-time 3`, the finite screen found 19,606 distinct
sender pairs, no profile or cut-budget failures, minimum fringe 14, and
maximum median-cut mismatch `16n` (against allowance `16.7936n`). These checks
are finite and use the ordinary unsaturated D2 flow; they do not establish
the sparse-bottom candidate's gates or the global sorting recurrence.

The direct identity audit
`d2_factor_identity_audit.py --depth 100 --row-bits 13` checks 206,594
ordinary positive-up senders. Every exact identity and role case passes;
the maximum observed `a/c` is `4193/4096`, and the maximum `g` is below
`1/512`. This closes the earlier simulator-versus-compressed-recurrence
verification gap only at finite depth; the all-depth identity and schedule
lemmas remain to be proved.

`parameter_cost_screen.py` scans the exact integer `FlowDAG` and now reports
the maximum `a/c` and its sender by role. At depths30 and100 the maxima agree:

| Role | Maximum `a/c` | Depth30 witness `(time,level)` | Depth100 witness `(time,level)` |
|---|---:|---:|---:|
| `topRise` | `4193/4096` | `(46,6)` | `(154,8)` |
| `botDesc` | `1` | `(4,2)` | `(4,2)` |
| `botRise` | `1/256` | `(3,3)` | `(3,3)` |
| `mid` | `8385/8192` | `(47,7)` | `(155,9)` |

The largest observed factor is about1.024, comfortably below9/8. At both
depths the minimum equivalent fringe is exactly `8192/559` rows, attained by
the mid sender. These are two exact finite scans, not evidence for all depths;
in particular, they do not address `topDesc`, leaf senders, or prove the
cut-boundary lemma.

Even if proved, this closes only the geometric input to a 13-row local tail
provider. Moreover, it does not instantiate the existing Lean provider:
`NodeGeom` requires `m=2*f+64*b`, `up=2*f*n`, `f=0` or even
`f>=131040`, and `m>2^42`, whereas this screen uses row height8192. A new
provider and compatible exact geometry are needed. There is a concrete
small-row obstruction even before those large-size guards: at depth30, the
sender `(t,i)=(41,3)` has `a=67,764,224` and `pi=245,760`, hence
`pi/(2a)=15/8272`. Exact shape `a=m*n`, `pi=2*f*n` forces `8272 | m`, so
no exact local rectangle with `m<=8192` handles this sender. The audit script
reproduces this witness. A 14-bit padded three-sort core would cost315 layers,
above the 300 target. This rules out the direct exact-shape 13-bit core for
this flow; it does not rule out partial-row geometry, a more efficient local
network, or a changed flow.

The uniform rank-tail probability bound, centered-ragged physical embedding,
root initialization, ordered global recurrence and terminal gate remain
separate obligations. The nominal coefficient273 is still conditional.

## Exceptional predecessor reserve (2026-10-22)

The schedule-side `botRise` reserve branch is now kernel-checked in the
standalone `D2ScheduleReserve.lean`. For the relevant boundary sender, its
children remain inactive while the parent is inactive or uses `botRise`; the
trace lemma proves their deficit remains native. That native value is exactly
one eighth of the later child capacity, giving the required `c/128` reserve
before the next ordinary cut. The lemma allows arbitrary child-port and
cut-deficit functions, so this is a schedule fact rather than finite-flow
evidence.

The focused check passes with `lake env lean
../prefix-flux/D2ScheduleReserve.lean` from `upper-bound/experiments/runaware`.
This closes only the exceptional predecessor branch. The ordinary branch
still needs actual cut-front containment and a nonnegative intermediate
child-port update. The quota sum itself is now handled at the schedule level
as described below; its use in the full flow still depends on native bounds
for every child and on the exact conservation identity. The full D2 flow and
sorting proof remain open, and the nominal coefficient273 remains
conditional.

## Schedule-derived quota-sum split (2026-10-22)

`D2ScheduleReserve.lean` now proves `d2_schedule_two_step_quota_roles` and its
factor corollary `d2_schedule_two_step_sender_factor_279`. For a regular
active sender with `t>=4`, the closed-form schedule places the intermediate
child level in `mid`, `botDesc`, or `botRise`. In the first two roles, the
eight normalized child quotas sum to at most `15/16` after the identity's
factor32. In the exceptional `botRise` case, native-size bounds give total
mass at most1, while the schedule forces the older sender to `botDesc` and
hence its old quota is exactly `15/4096`. This is the role split needed by
the `279/256` arithmetic lemma.

The corollary still assumes (i) native-size bounds for the older sender and
each intermediate child, (ii) the exact two-step conservation identity, and
(iii) the older/current normalized deficit caps. It closes the
schedule/quota algebra but does not establish these state invariants or link
the abstract recurrence to the full sorting construction. Focused verification
passes with `lake env lean ../prefix-flux/D2ScheduleReserve.lean` from
`upper-bound/experiments/runaware`.

The same file now proves `d2_schedule_ordinary_predecessor_noncrossing`.
When the sender two stages earlier has an ordinary role, its schedule quota
is at least `15/4096`; nonnegative intermediate child ports, the current
`g<=1/512` cap and port `<=1/256`, and the exact identity force the current
up-port to fit inside its allocation. The theorem is conditional on native
allocation bounds and the exact identity, but it removes a separate geometric
noncrossing obligation for this predecessor case. The exceptional `botRise`
predecessor remains handled by the trace theorem above. Neither case has yet
been composed with a single all-depth induction over the actual `FlowDAG`.

The exceptional trace branch also now has a compiled sender-factor corollary:
`botRise_parent_trace_sender_factor` gives `a/c<=1/16` two visits later from
the unchanged native children, two conservation equations, and a
nonnegative current deficit. Combined with the regular-predecessor theorem,
both predecessor cases now provide conditional noncrossing and sender-factor
interfaces. The outstanding part is establishing their hypotheses
simultaneously from the initialized actual flow, then proving the local
provider and global rank/terminal contracts.

The intervening-stage persistence is also now checked: parity makes a
same-level sender inactive at `t-1` whenever it is active at `t`, and
`d2_scheduled_endpoint_reserve_persists` composes this with the ordinary
half-port reserve transfer and a nonnegative child up-port. Thus neither
predecessor branch is missing a one-stage reserve-preservation fact; both
still depend on the actual old cut/reserve data and native/deficit invariant.

Repository inspection confirms the current Lean `FlowTable`/`FlowSizes7`
modules formalize the separate `(64,4096,1/64)` construction, not this
`(8,8,1/4)` D2 flow. `D2ScheduleReserve.lean` therefore remains a standalone
schedule/arithmetic model. An exact state/update representation for the new
flow, with an initialized coupled induction, is now the main formal bridge
before provider integration.
