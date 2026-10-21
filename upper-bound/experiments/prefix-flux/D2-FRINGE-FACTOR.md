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

The equivalent full-row fringe width is `m*pi/(2a)`. The D2 formulas give:

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
not just a numerical fit. This does not close the all-depth result: the
induction still has to establish the `g` bound, prove `rho<=1/256` for
`botRise` (ordinary roles have it from their formulas), and handle a
`botRise` predecessor, schedule startup, and leaf/boundary cases separately.
For a `topDesc` predecessor, the parent sets both end deficits to zero, so
the same identity has no `16*g+16*rho` term; that case is covered by the
child-rho bound alone.

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
provider. The uniform rank-tail probability bound, centered-ragged physical
embedding, root initialization, ordered global recurrence and terminal gate
remain separate obligations. The nominal coefficient273 is still
conditional. Fresh mathematical review of the invariant must precede Lean.
