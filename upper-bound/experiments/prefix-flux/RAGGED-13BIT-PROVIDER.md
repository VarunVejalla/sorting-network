# Paper test: heterogeneous 13-bit D2 columns

Status: promising geometric construction for the `(3,3,2)` route; not yet a
sorting theorem or a replacement Lean provider. No Lean changes are part of
this paper test.

## Motivation

`D2-FRINGE-FACTOR.md` gives a paper candidate for bounding every ordinary
sender by `a/c <= 9/8`. Combined with a 13-bit local core and the schedule rate
`(x+y)/(xz)=1`, its conditional coefficient is `3 * 91 = 273`. The existing
uniform `NodeGeom` shape is an obstacle: each sender must have
`a=m*n`, `up=2*f*n`, and `m=2*f+64*b`, but at depth30 the sender
`(t,i)=(41,3)` has `a=67,764,224`, `up=245,760`, and
`up/(2a)=15/8272`. No uniform exact shape with `m<=8192` handles it.

## Heterogeneous-column proposal

Allow each column `j` to have its own fringe width `f_j` and bulk-group count
`b_j`, with

```text
m_j = 2*f_j + 64*b_j <= 8192,
f_j >= 13,
a   = sum_j m_j,
up  = 2*sum_j f_j.
```

Interpret each column as two fringes of `f_j` wires and 64 interior groups of
`b_j` wires. Each of the 64 output groups then has total size
`B=sum_j b_j=(a-up)/64`. Sorting a column padded to 8192 wires uses a 13-bit
Batcher network of depth91; with fixed `-infinity` padding, deleting
constant-wire comparisons should give a sorting network on the real `m_j`
wires of no greater depth. The 13-row local-tail hypothesis is met in every
column. If the same local provider and three-sort schedule extend to this
heterogeneous geometry, the coefficient remains273.

For the obstructing sender, an exact realization is:

```text
n = 8307 columns
f_j = 15 for 6582 columns and 14 for 1725 columns
b_j = 126 for 13 columns and 127 for 8294 columns
pairing: the 13 columns with b=126 have f=15

2*sum(f_j) = 245760 = up
sum(64*b_j + 2*f_j) = 67764224 = a
min(m_j) = 8094; max(m_j) = 8158 <= 8192
```

`ragged_fringe_geometry.py` checks this decomposition with exact integers.

## Proof gates and possible failure points

1. Establish for every relevant sender the integer identity
   `a=up+64*B`, and choose a number of columns and integer pairs `(f_j,b_j)`
   with `f_j>=13`, `m_j<=8192`, and `sum f_j=up/2`, `sum b_j=B`. The current
   script checks only the displayed witness, not every role or depth.
2. Show the 64 output groups can be routed to exactly the portions required
   by the recursive D2 scheduler. Aggregate counts alone may not preserve its
   address and rank contracts.
3. Generalize the fringe probability and separator argument from one common
   `(m,f,b)` to varying `(m_j,f_j,b_j)`. The fact `f_j>=13` alone may not
   preserve every union bound, uniformity assumption, or simultaneous-witness
   step in the current proof.
4. Prove the padded 8192-wire column network restricts to a valid
   depth-91 comparator network on each `m_j`-wire column, then account for all
   three local sorting passes and any cross-column work.
5. Close the all-depth flow bounds, root initialization, global rank
   recurrence, and terminal purity from `D2-FRINGE-FACTOR.md`.

The exact witness removes the specific uniform-divisor obstruction, but does
not establish any of gates 1--5 beyond that one sender. Review the provider
generalization and recursive port compatibility before any Lean work.

## Independent review verdict (2026-10-21)

A fresh-context review confirms the integer witness exactly removes the
uniform-divisor obstruction for `(t,i)=(41,3)`: `sum f_j=122880`,
`sum b_j=1,054,976`, and each column height is 8,094--8,158. This is only
an arithmetic result for that sender.

The fixed-mask rectangle below resolves how to define one shared sample
space, though no distribution-preservation or port-semantic lemma is proved
yet. The key remaining local issue is a profile-conditioned port/rank
postcondition for the evolving padded mask, plus its probability bound and
union over both orientations.

Fastest gate: state the complete local postcondition for this one explicit
profile, define the shared random choice, and prove its total failure
probability is below1. If the current random variable cannot be defined for
this profile, stop this provider branch before generalizing to all senders.
The nominal273 coefficient remains conditional on this gate and the routing,
all-depth flow, global recurrence, and terminal-purity gates above.

## Sharpened next experiment

The geometry has only three column types: `(f,b)=(15,126)` in13 columns,
`(15,127)` in6,569, and `(14,127)` in1,725. The first decisive test can
therefore fix this exact ordered profile rather than union over all possible
assignments of column types. A natural sample space is the existing
`Scramble(8192,8307)^2`, with each input column's real wires in its prefix and
its remaining suffix tagged `-infinity`; use the deterministic specialized
three-sort network on the live wires.

State one profile-conditioned property for this fixed mask: it must give the
full D2 port/rank postcondition for every binary assignment to the live wires,
all 64 children, all required cuts, and both orientations. Prove its failure
probability is below1 for a single shared scramble pair. This removes the
ambiguity about what random experiment to test first. The B2 component has a
plausible relaxed parameter (`d=3/1250`, quantified below), but the complete
provider still needs the specialized-mask port postcondition, an F2 witness
at the actual `f_j` values, and the exact child-address map.

## Relaxed bulk bound at the explicit rectangle

The old bulk parameter `d=1/59000000` makes `failBoundB2` useless at row
height8192: its round-two exponent is only about `7.93e-8` per column,
versus a state/subset count cost about `9.70`. Relaxing the semantic spill
allowance makes the same bound pass. Set `m=8192`, `n=8307`,
`E1=371/10^8`, `lambda=1`, and B2 parameter `d=3/1250`. Then

```text
K = lambda*d/2 - lambda^2*(1/2+2*lambda/9)*E1
  = 2155177/1800000000,
m*K = 9.8084499911..., log(2*(m+1)) = 9.7041825908...,
log(failBoundB2 / |Scramble|) < -866.14.
```

The B2 semantic error is `d/2=3/2500=0.0012` of the padded rectangle;
including both orientations still leaves a tiny failure probability. This is
an outward-interval evaluation of the existing B2 bound, not yet a Lean
instance or an end-to-end profile theorem. It shows the bulk union bound need
not kill the 13-bit geometry if the global rank recurrence tolerates about
0.12% bulk spill. Column heterogeneity is not needed for this probability
calculation; it remains needed for the exact sender geometry.

### F2 companion screen

`ragged_provider_probability_screen.py` tests `J=17`,
`delta*f*n=18`, `(g1,g2)=(floor(2f/5),floor(4f/5))`, `c=1/2`, `b=5` at
`n=8307`. Its nominal minimum-dimension threshold is `J/(delta*f)=
17*8307/18 < 8307`, but the chosen interval estimates do not certify: R1a
and R2 conditions fail for both fringe widths. The generic Lean
`F2Pre.hf16` guard also reports false because it asks `delta*f*16>=1`; a
local-n formal variant would be needed to exploit the larger actual dimension.
This is one candidate parameter point, not an impossibility result for F2 or
the provider. The fringe estimate and its dimension-specific Lean interface
remain open; the relaxed bulk B2 estimate is numerically adequate.

## Fixed-rectangle realization of the profile

There is a concrete way to define the random experiment without independently
scrambling ragged columns: embed the fixed profile into one `8192 x 8307`
rectangle, put `-infinity` in each column's suffix, and choose the same two
row-scramble objects as for a rectangular provider. Interpret keys in
`-infinity < 0 < 1`. In every comparator touching a dummy, the dummy exits on
the low output wire regardless of the live key. Thus the set of live wire
positions evolves deterministically under the fixed three-sort network,
independent of the binary input. Specializing away dummy wires should compile
the full network to a network on exactly the live wires without increasing
depth; the per-column padded sort is the simplest instance.

This addresses the sample-space ambiguity at the construction level, but it
is not yet a provider proof. One must prove the full port postcondition for
that evolving deterministic live-wire mask, and derive its probability bound
from the scramble distribution. `HasPackSemanticPropertyB2/F2` as currently
stated concerns a full binary rectangle and does not directly give this
mask-conditioned contract or the exact 64 child address sets. This is now the
right first mathematical lemma to try: specialize `physicalPack2Net` to a
fixed live mask, prove its occupancy trace is input-independent, and identify
when its output live set can be partitioned into the required 64 equal ports.

### Explicit-mask cut transfer for the displayed profile

The fixed-mask gap has a promising deterministic reduction for the displayed
column profile. Write `h_j=2*f_j+64*b_j` and pad each column's `h_j` live wires
with distinct dummy keys smaller than every live key. In semantic coordinates,
each column sort puts the live wires in a suffix of length `h_j`; row scrambles
only permute the mask, and the next column sort restores a suffix. The final
live set is therefore fixed by the scramble pair and independent of the live
key order. Its suffix partitions into a lower fringe of `f_j`, 64 groups of
`b_j`, and an upper fringe of `f_j` wires. The group sizes are exactly
`sum_j b_j` in every group. In physical coordinates these sets are transported
by the cumulative row-scramble permutation.

For any fixed full comparator sequence, comparisons between a live wire and a
dummy wire route a live value along a path determined solely by the live mask;
comparisons between two live wires remain ordinary comparators. Deleting the
dummy paths and retaining the live-live comparisons gives the induced network
on the live inputs/outputs, with no larger depth. This is the intended
mask-extraction lemma. It must be formalized with the actual layered comparator
network and the physical/semantic row-scramble maps; the preceding paragraph
is its proof specification, not a Lean theorem.

The B2 cut guarantee transfers with a small exact charge. For a cumulative
cut after `q` middle groups, the per-column row boundary is

```text
r_j(q) = 8192 - f_j - (64-q)*b_j,       0 <= q <= 64.
```

Use the majority type `(f,b)=(15,127)` as a common row cut. The thirteen
`(15,126)` columns shift that cut by `64-q` rows each; the 1,725 `(14,127)`
columns shift it by one row each. Thus the symmetric difference of the
heterogeneous live-prefix cut and its common row-cut comparison set is at
most

```text
13*(64-q) + 1725 <= 2557 cells.
```

The exact geometry script also checks the stronger single-port symmetric
difference: at most 5,101 cells, attained by group 1. For the node cut
contract, the 2,557-cell cumulative-cut charge is the relevant one. With
`m=8192`, `n=8307`, the screened full-rectangle B2 error at
`epsB=3/1250` is
`(3/2500)*m*n = 81,661.1328` cells. Adding 2,557 gives
`84,218.1328`, below the local contract budget
`(1/800)*m*n = 85,063.68` (local `epsB=1/400`), leaving about 846 cells of
slack. `ragged_provider_probability_screen.py` reproduces this comparison and
the existing B2 interval screen (`log failure fraction < -866`).

For the F2 fringe contract, `f_j>=14` means that every upper fringe contains
the common last 14 rows of its column. Extend the live keys by distinct
smaller dummy ranks; then the largest `j` full-rectangle keys are live keys,
so the full-rectangle F2 event directly bounds their escape from the upper
fringe. The reversed-wire/flip-scramble argument gives the lower-fringe
version. The closed F2 screen at `f=14`, `n=8307`,
`(g1,g2,c,b,J)=(7,9,1/3,6/5,1)`, and `delta=18/(14*8307)` passes the
`1/1000` failure budget. The randomized full-rectangle events are universal
over input permutations, so the same good scramble pair covers the padded
dummy assignment; there is no additional union over masks for this one fixed
profile.

This closes only the explicit-profile *count-transfer* subgate on paper. The
mask extraction, its boundary wire bijections, and the F2/F2-flip application
have not been Lean-checked. The all-depth family of integer profiles, global
D2 rank recurrence, root, terminal cleanup, and limsup theorem remain open.

## Can first-round SR/R1 replace F2's second round?

No direct implication follows from the current SR/R1 thresholds. Paper
Property F asks for fewer than `(f/2) s + eps*j` hits in the top `m-f/2`
rows. SR/R1 constrain hits in the larger top `m-g1` region, with `g1≈0.4f`.
For `s≤κ_E`, R1b gives `< Δ s + B_E`; this suffices from thresholds alone
only when `B_E ≤ (f/2-Δ)s + eps*j`. For `s≥κ_E+1`, R1a can work by
restricting to `κ_E+1` columns, provided `Δ+1≤f/2`.

At the screened `f=14`, `g1=5`, `g2=11`, `J=17`, `b=5`, `c=1/2` point,
`E=2` gives `κ_E=1`, `Δ=6`, `B_E=10`. Singleton R1b gives `<16`, while F
needs `<7+eps*j`; SR gives only `<10`. For `j=8`, the total-mass bound is
also insufficient (`8` versus `7+8eps`). Thus the apparent one-round
shortcut has a low-rank gap, even before probability estimates. It needs a
separate direct estimate for these small-rank singleton events (or stronger
SR/R1); simply dropping R2 from the current proof is unsound. This is a
threshold audit, not a counterexample to the full F2 route.

## Re-screen with local dimension and shifted fringe cuts

The failed `J=17`, `(g1,g2)≈(0.4f,0.8f)` point was too restrictive. At the
actual rectangle width `n=8307`, put `δ=18/(f n)` and `J=1`. The existing
outward-interval script `walk-bound/fringe_cert_v2.py` certifies the closed
probability bounds for both widths with:

| `f` | `g1` | `g2` | `c` | `b` | `J` | closed `ln(2P1)` | closed `ln(2P2)` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 14 | 7 | 9 | 1/3 | 6/5 | 1 | -8.73133 | -6.97134 |
| 15 | 8 | 10 | 1/3 | 6/5 | 1 | -9.04436 | -6.97134 |

Both closed-form bounds pass `2P1,2P2≤1/1000` and satisfy the F2 precondition
`c+1/2≤b`. The shifts give `Δ=2`, `Φ=5`; the generic `E=2` term is covered
without a special case. P2 has the tightest margin: its log upper bound is
about 0.0635 below `ln(1/1000)`. This is a numerical gate passed for the
shared `n=8307` profile, not a theorem or provider result.

The script's Lean-friendly closed forms now pass, and `F2Pre.hf16` still fails
(`δ f·16=288/8307<1`). The independent API
review found only two proof sites that consume `hf16`: `jE_factsd` and
`SRd_fail_card_le`; replacing that global threshold with the local fact
`1≤δ f n` should expose the fixed-dimension case. The current generic Lean
`R1aNumd` and `R1bNumd` sufficient inequalities also fail here (their final
left sides are about `+5.3` and `-5.1`, against required `≤-15` and `≤-22`),
so the closed-form interval bounds need their own Lean proof path. Scratch
parameter lemmas are in `F2LocalDim.lean`; they check the scalar fields
excluding `hf16` and positive `jmax` locally, but are not yet Lean-verified.
The fixed-mask provider remains open.

**Review correction (2026-10-21).** A fresh review reran the exact positional
commands and confirmed that the closed-form envelope itself is valid. Its
narrowest margin is P2 at about `0.0636` below `ln(1/1000)`. The current
`R1aNumd`/`R1bNumd` predicates are still false (their final sides are about
`-1.95` and `-5.6`, versus `-15` and `-22`), because they demand per-event
`exp(-10E)` bounds. The passing script instead sums a different geometric
envelope directly; formalizing that aggregate route is the Lean gap, alongside
the local-`n` rank guard and concrete R2 finite/tail sums. For SR, the review
found the existing numeric interface can be localized with `K0=0`, `Xn=1`,
`qd=4`, `N=7`. No fixed-mask provider or global transfer has yet been proved.
