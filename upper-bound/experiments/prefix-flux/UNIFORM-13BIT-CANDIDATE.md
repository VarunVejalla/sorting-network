# A uniform-flow 13-bit route to coefficient 273

2026-10-21. Structural candidate, not a sorting theorem. The exact role
geometries below are checked by `uniform_13bit_geometry.py` through depth
100; the all-depth identities are derived from the uniform Chvatal formulas.
The local separator probability contract and the global sorting invariant
remain open.

## Candidate algorithm and price

Use the uniform Chvatal flow `U` with `(x,y,z)=(3,3,2)`, so `k=8`, `A=8`,
`nu=1/4`, and native family size `N=2^14*8^d`. The schedule has
`tf(d)=3d+O(1)`, while `log2 N=3d+14`; hence its stage rate tends to one.
At each ordinary sender, sort the row coordinate using three bitonic sorting
networks. The exact role-dependent row heights below are all at most `8192`,
so a 13-bit padded bitonic network gives at most

```text
3 * (13*14/2) = 273
```

comparators of depth per stage. Root handling and the final native blocks
have constant depth and do not change the limsup coefficient. The resulting
coefficient would be `273`, conditional on proving the required local
separator contract and the end-to-end sorting invariant.

## Exact uniform-flow port ratios

Write `c=Par.cap(d,i,t)`, `Q=A^2*k^2=4096`, and
`B=A*nu*k=16`. For positive-time active nodes, the uniform formulas give:

| Role | `a/c` | `up/c` | `up/(2a)` |
|---|---:|---:|---:|
| `topDesc` | `1` | `0` | `0` |
| `topRise` | `1` | `1/256` | `1/512` |
| `mid` | `4095/4096` | `15/4096` | `1/546` |
| `botDesc`, `native/c=1` | `4095/4096` | `15/4096` | `1/546` |
| `botDesc`, `native/c=1/16` | `255/4096` | `15/4096` | `1/34` |
| `botRise` | `15/4096` | `15/4096` | `1/2` |

For these parameters,
`native/c = 2^(4+2t-6i)`. The schedule endpoint is
`omega(t)=q+1` for `t=3q+1`, `q+2` for `t=3q+2`, and `q+2` for `t=3q`.
Thus `botRise` is `t=3q`, with `native/c=1/256`, and the two `botDesc`
cases have `native/c=1` and `1/16`, respectively. This supplies the row
ratios above without using a finite-depth fit.

## Role-dependent exact rectangles

Use a constant count inflation `S=2^14`. For a rectangle with `m` rows,
`n` columns, `f` fringe rows on each side, and equal `b`-row child blocks,
the desired exact equations are

```text
a = m*n,  up = 2*f*n,  down = b*n,  m = 2*f + 8*b.
```

The following choices meet these equations:

| Role | `m` | `f` | `b` | Resulting `n` at scale `S` |
|---|---:|---:|---:|---:|
| `topDesc` | `8` | `0` | `1` | `S*c/8` (root handled with `a=N`) |
| `topRise` | `8192` | `16` | `1020` | `2c` |
| `mid` | `8190` | `15` | `1020` | `2c` |
| `botDesc`, `native/c=1` | `8190` | `15` | `1020` | `2c` |
| `botDesc`, `native/c=1/16` | `8160` | `240` | `960` | `c/8` |
| `botRise` | bypass | — | — | all wires go up (`up=a`, `down=0`) |

For every active level, `c` is an integral power of two. The alpha cutoff
implies `c>=128`; therefore the displayed column counts are integers and are
at least16. The root at `t=0` separately has `a=N`, `up=0`, and eight equal
down blocks, fitting the 8-row `topDesc` shape. The equal-block equations
follow from the uniform flow's equal child allocations. No arbitrary-cut
interpolation or D2 deficit profile is needed for this geometry.

The finite script

```text
python upper-bound/experiments/prefix-flux/uniform_13bit_geometry.py --depth 100
```

checks every scheduled role through depth100 with the exact rational
`Par.alloc`, `Par.up`, and `Par.down` formulas, including divisibility,
`n>=16`, the child block equations, and the 273 depth calculation. This is a
reproducible finite check; it is not the proof of the formulas above.

## Remaining gates before Lean

1. Prove the uniform-flow role classification, endpoint ratios, integer scale
   conditions, terminal native-size bound, and stage-rate bound for all `d`.
2. State and prove the local probabilistic separator contract for `k=8` and
   these small row sizes/fringes (`f=15,16,240`; topDesc and botRise are
   special). The current checked `TwoRoundSeparatorExists` is for 64-way
   geometry with large `m` and large `f`; it does not instantiate here.
3. Close the global rank/tail recurrence and root initialization using the
   actual uniform-flow separator; a nominal local price does not prove sorting.
4. Prove a constant terminal cleanup and arbitrary-`n` padding cost, then
   formalize the parameterized family and limsup bound.

This route looks structurally cleaner than the D2 `(3,3,2)` candidate because
its ordinary port ratios have small exact denominators. It replaces the D2
exact-geometry obstruction, but it does not remove the probability or global
invariant gates. Fresh-context algebra review completed 2026-10-21
(`uniform_geometry_review`, GPT-6-Luna). It independently checked the ratios,
rectangle equations, divisibility, minimum column counts, and 273 cost. One
convention is essential: for `botDesc` and `botRise`, `native` in `a` is the
current-node mass `8^(d-i)`; the child-flow `down` term uses the next smaller
power. Under that convention, the listed residues and ratios are correct.
The review found no algebraic counterexample, but did not certify the
all-depth schedule claims or the end-to-end sorting result.

The immediate decisive paper gate is a uniform local separator theorem for
the exact k=8 rectangles listed above, with a postcondition strong enough to
compose through the static ordered ports. This is separate from the geometry
arithmetic. Formulate that theorem with explicit hypotheses and output ranks,
then test whether its probability budget is compatible with the global
rank-tail recurrence. Also prove by schedule induction that the role/residue
cases exhaust every active node and `c>=128`; the depth-100 script is
regression evidence only.

### First probability screen

`uniform_13bit_probability_screen.py` tests the existing F2 interval envelope
at the critical `f=15` fringe with `(g1,g2,c,b,J)=(6,12,1/2,5,17)`, retaining
the exact `E=2` support count. It fails at `delta=10^-11` and larger tested
values, and passes at `delta=10^-12` and `10^-13`. This is a useful feasibility
signal only: it is not a formal theorem, the current Lean API has the large-f
guard, and the rank fraction is extremely restrictive. The immediate question
is whether the actual global rank-tail recurrence can use `delta<=10^-12` at
all relevant stages; absent that, this is not a viable k=8 provider. Any
common-witness union over base rows must also be included in the probability
budget. This is already a serious transfer warning: at `delta=10^-12`, the
minimum columns from the geometry screen give `floor(delta*f*n)=0` in every
positive-fringe role. The minima are `n=8192` for `f=16`, `n=16384` and
`65536` for the two `f=15` cases, and `n=1024` for `f=240`. The geometry
screen counts 25,430 `(time,level)` cases with zero support cap over depths
3 through100, mostly the `mid` role. Thus the tested F2 small-rank clause
would handle only zero residual mass in those cases. This does not rule out
other large-rank clauses, but a global proof must close those stages without
using the small-rank estimate.
