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
exactly on 2,646 matching ordinary transitions in the typed D2 simulator at
depth30.

It yields a particularly simple sufficient invariant. If, on these
transitions, `g_x(t-2) <= 1/256`, `rho_x(t-2) <= 1/256`, and each child
`rho_y(t-1) <= 1/256`, then nonnegativity of `g_x(t)` gives

```text
a_x(t)/c_x(t) <= 16/256 + 16/256 + 32*8/256 = 9/8.
```

The depth30 typed scan sees `max rho = 1/256` and `max g =
983033/536870912 < 1/256`, so these are plausible exact invariant bounds,
not just a numerical fit. The all-depth fringe argument reduces to proving
the `g` induction and the explicit schedule cases below. For a `topDesc`
predecessor, the parent sets both end deficits to zero, so the same identity
has no `16*g+16*rho` term; that case is covered by the child-rho bound alone.

The special cases have a compact prospective treatment. For these parameters
and `t>=3`, `botRise` occurs at `t=3j`, `i=omega(t)=j+2`. Therefore

```text
native(i) / (scale * cap(i,t)) = 2^(4 + 2t - 6i) = 1/256,
```

and the generic capacity bound `a<=native(i)` proves `rho<=1/256` for every
`botRise` sender. If an ordinary sender's previous active time `t-2` was a
`botRise`, then `t=3j+2`, `i=j+2`, so the same capacity argument gives
`a/c<=native/c=1/16` at the current time. When an ordinary sender has no
active sender at `t-2`, the only positive-up startup case in the schedule is
`(t,i)=(2,2)`, also with `native/c=1/16`; `t=1` is the explicit `topRise`
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

Induct on stage `t` for `g_x(t)<=1/256` at ordinary senders. The root's
initial update sets its children to zero. A `topDesc` parent also sets the
child deficit to zero. An ordinary parent gives
`g_child <= g_parent/2 + rho_parent/4 <= 3/1024 < 1/256`, using the exact
capacity ratio `cap(child,t)/cap(parent,t-1)=2` and the role formulas
`rho_parent<=1/256`. This closes the only `g` hypothesis used by the
two-step identity.

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
`t-2=3j`, `i=j+2`, and `native/c=1/16`, so `a/c<=1/16` directly. The
remaining startup sender `(t,i)=(2,2)` has the same native/c bound; `t=1`
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
