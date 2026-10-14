# Audit of the tapered frontier, terminal, and row-lattice rules

Status: independent mathematical audit of the current candidate sources.  This
is not a Lean theorem and does not establish a sorting bound.

## Conclusion

The real capacity identities behind 945 are internally consistent, but the
present induction cannot start at stage 3 and then use only
`candidate_interior_child_flow_exists`.  Two exceptional transitions recur
throughout the schedule, rather than only at the finite bootstrap:

1. whenever `alpha(t+1) = alpha(t)-1`, the new upper bag has no parent
   contribution;
2. whenever `omega(t+1) = omega(t)+1`, the new lower bag has no child
   contribution.

This does **not** require nonempty exterior halo bags.  The static-debt repair
verified in `FrontierDebtFlow.lean` gives the upper frontier occupancy
`C+(16/15)eC`, the bottom frontier its opposite debt correction, and strict
interior bags occupancy `(1-1/Q)C`.  The corrections cancel exactly over every
complete active subtree.  The open mathematical gate is the corresponding
identity at arbitrary recursive rank cuts.

There is also a direct integer geometry mismatch.  `LocalIntegerFlow`
rounds arbitrary wire counts, but the only constant-depth provider for a large
ordinary bag currently requires a `NodeGeom`, hence a common column divisor
of the input, up-flow, and every equal down-flow.  The local integerizer proves
no such divisor.  Its one-wire rounding normally destroys it.  The finite
bootstrap/reset tables avoid this by exact power-of-two factorizations; no
scalable exact-factor analogue is present.  Nearby-rectangle padding followed
by `restrictWires` is a plausible repair that preserves the ±69 flow counts
and moves this cost into separator boundary estimates.

Consequently 945 remains arithmetically possible, but the scalar frontier
table is insufficient: the address debt forces a bottom-occupancy correction
whose naive absolute cost exceeds the currently screened margin.  A signed
frontier rank proof or a debt reset is now a genuine feasibility gate.

## Follow-up: static-debt cancellation

The static debt repair is now formalized in `FrontierDebtFlow.lean`,
`SubtreeMass.lean`, and `FrontierPrefixMass.lean`. With
`T(C,e)=C+(16/15)eC` and `L(B,C,e)=B-C/Q-(16/15)eC`, complete descendant
subtrees have exactly the bottom mass `L`; subtracting those subtrees from a
parent prefix leaves precisely the top-advance child mass, child by child.
Summing proves the same cancellation for every prefix made of whole child
subtrees. This closes the concern that the `q_j` correction must be charged
unsigned at such boundaries.

It does not yet establish the rank invariant. A cut inside a child requires
the recursive partial-prefix bound for that child's own descendants, plus an
outsider bound on keys stored outside the current parent subtree. The generic
three-way cover lemma in `FrontierRankCounting.lean` supplies the finite-set
counting step once those hypotheses are available; no current theorem has
instantiated it for the recursive scheduler.

## Exact frontier cases

Write `a_t = candidateAlpha d t`, `w_t = candidateOmega t`, and let
`C(l,t)=2^(6d+6l-4t-8)`.  Scheduled levels have the parity of `t`, so adjacent
scheduled levels differ by two.

The interior theorem assumes `l+2 <= w_t`.  It therefore covers all scheduled
parents except `l=w_t`.  It also only creates level `l+1` from a currently
active level `l`.  These facts leave the following cases.

| Frontier motion | New target | Interior theorem? | Required frontier rule |
|---|---:|---|---|
| `a_{t+1}=a_t+1` | level `a_t+1` | yes, except when the band has no two-level lower support | ordinary parent and grandchildren |
| `a_{t+1}=a_t-1` | level `a_t-1` | no | old top sends `C/65536` up; no parent block |
| `w_{t+1}=w_t-1` | level `w_t-1` | yes via parent `w_t-2` | none, provided the old bottom bag at `w_t` has a flow |
| `w_{t+1}=w_t+1` | level `w_t+1` | no | old bottom sends the complete next-bottom allocation down; no child up-flow |

The exceptional motions are recurrent.  For example, at `d=14`, upper
retreats occur at `t=1,3,5,7,9,14,20`, and lower expansions occur at
`t=1,2,4,5,7,8,10,11,13,14,16,17,19,20` (within `t<22`).  Thus the stage-two
reset is not a general frontier rule.  Once the unclipped upper formula is
positive, its `+1,+1,-1` pattern continues; the lower frontier similarly has
repeated expansions and contractions.

The narrow-band cases also need explicit handling.  When `a_t=w_t`, there is
one active scheduled level and the interior premise fails.  When
`w_t=a_t+2`, the upper parent has just enough lower support, but the bottom
bag itself still has no successor rule on an expansion.

## Conserved frontier allocation

Let `B(l)=N/64^l` be the number of native wires below one level-`l` bag and
let `Q=2^24`.  The direct analogue of `Schedule7.allocation` is

```text
top:       A_top(l,t) = C(l,t)
interior:  A_mid(l,t) = (1-1/Q) C(l,t)
bottom:    A_bot(l,t) = B(l) - C(l,t)/Q.
```

These allocations conserve the global `N` by a weighted-level identity, as
in `Wires31.total_mass`.  They also show why a physical two-level halo is the
wrong repair: adding positive occupancies below the bottom frontier would add
new weighted mass `64^l A(l,t)` on top of `N`.  The capacities there are
larger, not spare storage.  A halo could only be bookkeeping for virtual
deficits, not additional wires or ordinary separator bags.

Put `s=255/2^24`, the ordinary up coefficient.  Ignoring integer discrepancy
and address debt, the frontier rules are:

```text
upper advances:  up = 0,       each down = C/64
upper retreats:  up = C/65536, each down totals (C-up)/64
lower expands:   up = s*C,     each down = A_bot(l+1,t+1)
lower contracts: up = A_bot,   down = 0.
```

For the tapered unequal child profile, “each down totals” at a rising upper
frontier should use the same endpoint/middle widths plus signed debt as the
ordinary flow, but with the upward correction `+C/Q`.  Indeed

```text
s*C + C/Q = (255/2^24 + 1/2^24) C = C/65536.
```

This is exactly the correction already proved for the exceptional bootstrap
in `address_bootstrap_integer_split`; it should be generalized from the seed
to every upper retreat.

The lower-expansion identity is also exact.  Since
`C(l+1,t+1)=4C(l,t)` and `B(l+1)=B(l)/64`,

```text
(A_bot(l,t) - s*C)/64
 = (B(l) - C/Q - 255C/Q)/64
 = B(l)/64 - 4C/Q
 = A_bot(l+1,t+1).
```

Thus no inactive grandchildren are needed.  On a lower contraction the old
bottom sends all of `A_bot` upward, and the next bottom receives it together
with the ordinary block from its parent.  The final meeting case combines a
top-descending parent and a bottom-contracting child exactly as in
`FlowTable.flow_conservation7`; it needs its own tapered identity because the
new bag is simultaneously top and bottom.

These equations settle only the debt-free scalar count feasibility.  The
strict-interior `|eta|<=69` invariant should not be imposed on frontier
occupancy itself.  The next subsection gives the required debt-sensitive
replacement.

## Superseded debt-reset attempt

Let `e(b)=bagAddressDebt b`, with

```text
e(child_j) = (q_j + e(parent)/64)/64,
sum_j q_j = 0,
sum_j e(child_j) = e(parent)/64.
```

Using the ordinary signed up-flow at a boundary without correction fails.  In
particular, 64 upper children with capacity `1024*Cnew` deliver
`Cnew - 16*e(parent)*Cnew`, not `Cnew`.  This error is proportional to capacity
and cannot enter the 69-wire discrepancy.

A possible repair considered here was to reset normalized debt to zero at each upper frontier
and generate debt only below it.  Then define

```text
T(C) = C                                           (upper occupancy)
M(C) = (1-1/Q) C                                  (interior occupancy)
L(B,C,e) = B - C/Q - (16/15)eC                    (lower occupancy).
```

Here `B=N/64^l`, `Q=2^24`, and `s=255/Q`.  The full real sends are:

```text
upper advance:
  up = 0
  down_j = (r_j + 4/Q) C

upper retreat:
  up = (s + 1/Q) C = C/65536
  down_j = r_j C

lower expansion:
  up = sC - eC
  down_j = L(B/64, 4C, e(child_j))

lower contraction:
  up = L(B,C,e)
  down_j = 0.
```

The upper split identities use
`sum_j r_j = 64*rBar = 1-256/Q`.  Hence advancing down-blocks sum to `C`,
and retreat sends satisfy `(s+1/Q)C + 64*rBar*C=C`.  An advancing target is
also exact: ordinary grandchild up-flows plus
`(r_j+4/Q)C` give `4C`, after resetting the new top debt to zero.

For the bottom, write a provisional correction `lambda*eC`.  Expansion
conservation forces

```text
lambda/16 = lambda + 1,
```

so `lambda=-16/15`.  Explicitly,

```text
sum_j L(B/64,4C,e(child_j))
  = B - 256C/Q - (1/15)eC
  = L(B,C,e) - (sC-eC).
```

For contraction, the ordinary parent block plus the 64 lower child sends is

```text
B - C/Q + (16*lambda+16)eC = B - C/Q + lambda*eC,
```

again because `15*lambda=-16`.  Thus the correction is forced, rather than a
free reserve choice.

At the final meeting, the upper-parent block has an extra `C/Q` relative to an
ordinary block.  This cancels the scalar bottom deficit, but leaves
`lambda*eC`.  A final address-dependent upper block correction
`-4*lambda*e_new*Cparent` cancels it; its sum over the 64 new addresses is zero,
so the old upper bag still splits exactly.  This meeting rule needs a separate
nonnegativity and rank proof.

The correction is numerically material:

```text
(16/15)*eAbs = 31/251596800 = 1.2321301e-7
(16/15)*ePos =  1/8110080   = 1.2330335e-7
mu                         = 2.3754525e-7
screenedMargin             = 2.5400272e-8.
```

It also introduces a denominator `15`.  Since the candidate capacities and
address debts are dyadic, `L(B,C,e)` is not generally an integer.  The natural
scheduler must round bottom occupancies coherently, define expansion blocks by
the already selected child occupancies, and put the residual into the bottom
up-flow while preserving evenness.  Local independent rounding is not enough
because total mass and the later contraction must use the same witnesses.
This looks compatible with a bounded additive discrepancy, but no current
lemma proves it.

Charging `|(16/15)e|C` as a new independent outsider error makes the current
screen negative by about `9.78e-8`.  Therefore the existing scalar margin does
not automatically accommodate the debt-sensitive bottom frontier.  Feasibility
requires one of:

1. a signed bottom rank argument in which `-(16/15)eC` changes the native
   window endpoint and cancels an existing debt term, rather than being charged
   absolutely;
2. a debt reset before the lower frontier, with a mass-conserving transition
   layer whose own rank cost fits the margin; or
3. retuned `mu`, `delta`, or row threshold with a newly positive complete
   screen.

This reset model is not the preferred repair.  A moving reset changes the debt
assigned to the same deeper address from one stage to the next, so the displayed
contraction equation does not by itself connect consecutive target
occupancies.  The static construction below avoids that time-consistency gap.

## Static-debt frontier repair and subtree cancellation

`FrontierDebtFlow.lean` checks the local real-flow equations for the following
static model.  Put `kappa=16/15` and retain the original, time-independent
`addressDebt`:

```text
T(C,e)   = C + kappa*e*C
M(C)     = (1-1/Q)C
L(B,C,e) = B - C/Q - kappa*e*C.
```

The four frontier sends are

```text
top advance:  up=0,
              down_j=(1/64+kappa*(q_j+e/64))*C
top retreat:  up=(1/65536+e/15)*C,
              down_j=(r_j+e/64)*C
bottom expand: up=(s-e)*C,
               down_j=L(B/64,4C,e_j)
bottom contract: up=L(B,C,e), down=0,
```

where `e_j=(q_j+e/64)/64`.  The checked identities verify every split and
receive equation.  Positivity also has comfortable scalar room: at top advance
the worst coefficient is `1/64+kappa*qEnd+kappa*e/64`, still about `0.015616`;
top-retreat up is about `1.5259e-5 C` with a debt perturbation below `8e-9 C`.
Natural-number rounding and evenness remain separate obligations.

The apparently fatal top-advance term `kappa*q_j*C` is approximately
`7.9e-6 C` at an endpoint, far above `mu*C`.  It must not be treated as an
outsider error.  Its candidate cancellation is an exact native-subtree mass
identity.

Let a top bag `v` have capacity `C`, debt `e`, and let the bottom frontier be
`h` tree levels below it.  Capacity grows by 64 per tree level, so every bottom
descendant has capacity `64^h C`.  Iterating

```text
sum_j e(child_j) = e(parent)/64
```

gives

```text
sum_{w descendant of v at depth h} e(w) = e/64^h.
```

Therefore the complete debt correction within the active subtree is

```text
top correction + bottom corrections
 = kappa*e*C
   - kappa*(64^h*C) * sum_w e(w)
 = kappa*e*C - kappa*e*C
 = 0.
```

Strict interior occupancies contain no debt term.  Hence each complete active
subtree has exactly the same total mass as the scalar Chvatal allocation.  The
same identity holds separately below any newly created top child, using that
child's static debt.  This establishes why the `q_j` correction is a
redistribution between the top bag and its bottom descendants, rather than
new mass.

This is sufficient for total conservation but not yet for the rank induction.
The required theorem is a **cut version** of the identity.  For each prefix of
top child addresses, prove that:

```text
actual wires in the union of those child active subtrees
  = scalar native-subtree mass for that prefix,
```

with the top prefix correction

```text
kappa*C * sum_{j<p} (q_j + e/64)
```

cancelled by the summed bottom corrections in exactly those same descendant
subtrees.  This follows algebraically if the prefix is a union of complete
child subtrees.  It does not automatically cover an arbitrary ragged cut
inside a child subtree; that case needs the recursive prefix identity plus the
existing signed prefix/suffix debt bounds.

The viable outsider induction should therefore measure native population in
the **whole active subtree rooted at a bag**, not in the frontier bag alone.
At a top separator cut, charge only keys crossing between these corrected
native subtrees.  Charging the raw top block displacement against `mu` would
reject a redistribution that the bottom reserve exactly repays.

Two concrete proof gaps remain:

1. connect the scheduler's physical ownership sets to the complete-subtree
   partition, so that the algebraic cancellation concerns the same keys used
   by the rank invariant;
2. prove the recursive cut identity for partial descendant prefixes and show
   that its uncancelled endpoint term is already included in `reserve`, rather
   than adding another `kappa*eAbs` charge.

Until the second lemma is proved, neither 945 nor the conservative fallback
may assume that only one absolute frontier-debt charge is needed.

### Exact full-child-prefix counting bridge

For a top bag `u` at stage `t`, fix `1 <= p <= 63`.  Let `w_j=u.child j`, and
define

```text
K       = regs(u)
S_j     = subtreeKeys(placement_t, w_j)
S_<p    = union_{j<p} S_j
N_<p    = union of the native key intervals of w_0,...,w_(p-1)
D_j     = the actual integer top-advance block sent toward w_j
O_<p    = |S_<p \ N_<p|.
```

The placement partition gives `Disjoint K S_<p`; distinct child subtrees are
also disjoint.  Native intervals of the children are disjoint and each has
cardinality `B/64`, so `|N_<p|=pB/64`.  The schedule-specific form of
`top_advance_native_child_mass`, after coherent integer rounding, must give

```text
|S_j| = B/64 - D_j,
|S_<p| = pB/64 - sum_{j<p} D_j.
```

Hence

```text
|K ∩ N_<p| <= sum_{j<p} D_j + O_<p.                 (P)
```

The proof is pure finite-set counting: `K∩N_<p` and `S_<p∩N_<p` are disjoint
subsets of `N_<p`, while
`|S_<p∩N_<p|=|S_<p|-|S_<p\N_<p|`.  This is now packaged as
`native_count_le_of_disjoint_storage` in `FrontierRankCounting.lean`.

If integer blocks satisfy
`D_j <= frontierTopAdvanceDown(C,e,j)+rho`, then (P) yields

```text
|K ∩ N_<p|
 <= p*C/64
    + kappa*C*(sum_{j<p} q_j + p*e/64)
    + p*rho + O_<p.                                 (SP)
```

This is the desired signed prefix width.  The endpoint-sized `q_0` term is
inside the native width in (SP); it is not included in `O_<p` and is not
charged to `mu`.  The suffix statement follows by using children `p,...,63`
or subtracting the prefix from the exact total.

The remaining hypothesis is a genuine higher-order outsider estimate.  For
each descendant bag `z` in the subtree of `w_j`, put
`r=z.l-w_j.l`.  A key in `regs(z)` that is not native to `w_j` is an
order-`r+1` stranger of `z`, because `z.ancestor r=w_j`.  Disjoint placement
therefore gives

```text
O_<p
 <= sum_{j<p} sum_{z in subtreeBags(w_j)}
      z.strangers (z.l-w_j.l+1) id (regs z).
```

This statement needs three explicit scheduler facts: every key in `S_j` has a
unique owning descendant bag, `ancestor (z.l-w_j.l) z = w_j`, and the outsider
invariant is available at all orders through the terminal depth.  An
order-one bound only on each active bag is insufficient.  The numerical
induction must prove that the displayed double sum is at most the proposed
subtree budget (including integer rounding); otherwise (SP) does not close.

No ragged separator cut is needed for this step: `p` is a boundary between
complete child subtrees.  Ragged physical cuts enter later when (SP) is
converted into the local separator's output-slot window.

### Conservative 999 screen

The proposed fallback (`epsB=3/10^7`, row range `2^35..2^36`) retains adequate
fringe scale.  The old candidate has about 130,560 fringe rows at `2^34`; the
same ratios at `2^35` give about 261,120, above both the established 92,160
floor and `1/(656*epsF)` (about 12,814 for unchanged
`epsF=511/2^32`).  Top-advance zero fringe and bottom-contraction zero down-flow
need their directional sorter cases, as in the standard frontier shapes.

Numerically, charging one full `kappa*eAbs` plus `200/2^35` is compatible with
the reported 999 scalar screen.  The audit cannot yet certify the factor one:
a complete subtree cancels exactly, while an arbitrary partial window can
temporarily expose a top correction and only part of its bottom repayment.
The recursive cut identity above must show that the exposure is at most one
`kappa*eAbs` (or produce the actual larger factor) before 999 is a conservative
theorem target.  Subject to that gate, three 1998-layer stages per six bits do
give coefficient 999.

## Row-lattice obstruction

For a large bag, the current network provider `nodeGood_geom` requires

```text
a    = m*n,
up   = 2*f*n,
down = b*n,
2^42 < m <= 2^43,  and  16 <= n.
```

Thus `n` divides all routed block sizes (and `up`), and for a growing wire
count it is itself large: `a/2^43 <= n < a/2^42`.  In contrast,
`LocalIntegerFlow` only proves that `up` is even and that each block is within
`1+70/64` wires of its real target.  It supplies no `n>=16` common divisor.
An independently rounded block can have gcd one with the other blocks.  For
bags above `2^63`, the small-bag bitonic provider is unavailable, so the
existing sources do not produce a network for such a split.

### Padding to a nearby rectangle

Padding each large local bag to a nearby `m*n` rectangle is a credible way to
avoid requiring the *flow counts themselves* to share a column divisor.  Pick
a power-of-two `n` near `a/2^34` and put

```text
a' = ceil(a/n)*n,       r = a'-a < n,       m = a'/n.
```

With the choice made carefully, `2^34 <= m <= 2^35` (allowing a one-row
endpoint adjustment).  Move requested cuts and fringes to row boundaries.
Each moved boundary costs less than `n` cells, so two shifted boundaries cost
less than `2n`; normalized by `a' = m*n`, this is below `2/m`, hence about
`2^-33`.  This is the right scale for the candidate screen and is much smaller
than treating a whole row as `69/2^34`.  The depth is indeed at most
`3*T(35)=1890`, since `pack2_depth_le` depends on `m` and not on `n`.

This removes the divisor obstruction without changing the selected flow
counts.  `AKS.Sort.Shrink.restrictWires` filters every comparator touching the
padded suffix.  Its execution lemma proves, for Boolean inputs padded by
`true`, that the suffix remains `true` after every ordered comparator and the
prefix execution agrees exactly with the restricted network.  This also
applies to the physical pack: its relabeled comparators still have increasing
endpoints.  Padding therefore does not require dynamic sentinel locations and
does not force `LocalIntegerFlow` to round in row-sized units.

Choose the desired live `up` and child blocks first, restrict the padded
physical network to the live prefix, and use those exact live cuts.  Compare
each physical cut inside a matrix row with a neighboring row-aligned cut,
costing less than `n` cells per boundary.  This surcharge belongs in the
separator rank estimate; it is not occupancy discrepancy.  The `|eta|<=69`
flow recurrence can in principle remain unchanged.

The padding route still has three proof obligations:

* The checked `TwoRoundSeparatorExists` interface only covers
  `2^42 < m <= 2^43`, and its bulk constant is `1/59000000`.  The 35-bit-row
  padding needs the proposed Variant B theorem at `m>=2^34`, with the candidate
  `epsB=2^-21`.  The numerical screen is not yet that theorem.
* The restriction execution lemma is private and Boolean-specific.  The
  candidate needs a public NodeSpec transfer, or a local reproof, for both
  boundary directions.
* The arbitrary-cut theorem must track the exact loss: `<n` for one boundary
  and potentially `<2n` for a two-boundary window, separately through B2,
  fringe, and variable-window estimates.
* Although prefix execution is exact, NodeSpec on the padded arity uses ranks
  relative to `a'`.  The transfer must charge the suffix size `r<n` wherever
  an upper cohort threshold shifts.  This is also a correctness charge, not
  routed mass.

Nearby-rectangle padding is therefore the preferred geometry repair.  It
allows each bag to choose its own `(m,n)`, avoids cross-sender divisor
coherence, preserves the exact ±69 wire scheduler, and charges only
`O(n)/a'=O(1/m)` to separator correctness.  The total aligned-cut and rank
shift constant must still be screened against the claimed `2.54003e-8`
reserve.

## Terminal rule and coefficient

At `t=tf=3d-20`, both frontiers equal `d-6` and
`C(d-6,tf)=2^36`, matching the native interval size `64^6`.  This is a fixed
size, so a bitonic terminal sorter has constant depth (the existing small-node
budget applies below `2^63`).  This supports an additive terminal cost.

It does not yet prove termination correctness.  The ordinary invariant allows
a positive outsider count at capacity `2^36`; sorting each terminal bag does
not move outsiders between terminal bags.  A terminal theorem must prove
purity, or give a bounded-depth cleanup across a bounded number of neighboring
terminal bags.  Such a cleanup can remain additive because all terminal
scales are fixed, but neither rule is currently present.

The leading calculation itself is correct conditional on these repairs:
three stages of depth 1890 per six input bits give
`3*1890/6 = 945`.  To retain it, root work, lattice resets, and terminal cleanup
must occur only `O(1)` times per root-to-leaf path, while every recurrent
frontier shape must execute within the already charged ordinary stage.

## Feasible induction plan

1. Define one address-indexed allocation table with `T(C,e)`, `M(C)`, and
   `L(B,C,e)`, zero outside the active band.  Prove both per-address
   conservation and the weighted total `N`; the latter uses cancellation of
   the debt sum across every complete level.
2. Prove one conservation theorem with the four Chvatal-style shapes: upper
   advance/retreat and lower expansion/contraction, plus the narrow and final
   meeting cases.  Generalize `address_bootstrap_integer_split` to every upper
   retreat and integerize the bottom reserve formulas.
3. Build each large local network by padding to its own nearby 35-bit-row
   rectangle and restricting the padded network.  Preserve the wirewise ±69
   schedule and charge row alignment only in separator correctness.
4. Prove signed frontier rank/outsider lemmas using the corrected top and
   bottom occupancies.  Establish the recursive prefix cancellation and bound
   its endpoint exposure; otherwise rescreen the parameters before continuing.
5. Prove a terminal purity or bounded-neighborhood cleanup lemma at level
   `d-6`, and only then derive the maximum-path recurrence.

The decisive next experiment is a six-stage symbolic/integer frontier cycle,
because it contains both frontier directions and the parity cycle.  It should
track exact natural counts, signed debt, and the padding boundary surcharge.
Failure to close that finite cycle would be a concrete obstruction to the 945
scheduler; success would provide the repeating global rule missing from the
current stage-three reset.
