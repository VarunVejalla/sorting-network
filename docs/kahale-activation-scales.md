# Growing activation orders: exact model and first rate screen

Follow-up: [preparation charges and residual sorting problems](kahale-certificate-preparation.md)
shows that the full certificate potential has amortized growth rate `3/2`
on a depth-logarithmic prefix family. The current structural lead measures
sorting difficulty remaining in the actual Boolean image.

This extends [the joint routing-group investigation](kahale-joint-groups.md).
The hypergraph identities below are derived mathematical arguments; the
finite checks are Python enumeration. Neither is a new Lean theorem or an
improvement on the checked coefficient 3.270559454.

## Exact state and transport

For a monotone wire function `f` and a baseline one-set `S` with `f(S)=0`,
let `H_f(S)` consist of inclusion-minimal sets `E` outside `S` such that
`f(S union E)=1`. A zero certificate valid at `S` is exactly a hitting set
of this hypergraph: a set `C` outside `S` forces zero precisely when
`f([n] minus C)=0`, equivalently when it meets every minimal activation.
Thus the full transversal number is the conditional certificate size.

For a comparator whose two baseline bits are zero, its hypergraphs update by

```text
H_AND = inclusion-minimal { E union F : E in H_a, F in H_b }
H_OR  = inclusion-minimal (H_a union H_b).
```

Indeed, an activation of AND contains an activation of each child;
an activation of OR contains an activation of at least one child. For mixed
baseline bits the minimum inherits the zero child's hypergraph, and the
maximum is already one. At baseline `11` neither output contributes.

Retaining only edges of size at most `L` is closed under these comparator
updates: a union of size at most `L` cannot use a larger child edge.
This gives an exact order-`L` state, rather than a guessed moment closure.

There is also an exact constraint between adjacent baselines. If
`f(S+p)=0`, then

```text
H_f(S+p) = inclusion-minimal { E minus {p} : E in H_f(S) }.
```

This follows by expanding an activation at `S+p` to an activation at `S`,
and conversely. To compute the truncated order-`L` state at `S+p`, the
order-`L+1` state at `S` suffices. The script also independently checks this
identity for every distinct reachable wire function. It is the concrete coupling
between input weights and activation orders that a new inequality can use.

## Potential and endpoint

Let `K_L(P)` sum the transversal numbers of the order-`L` hypergraphs over
all wires and all zero baselines of a prefix `P`, with each baseline counted
once. Initially all nonempty activation hypergraphs are singletons, so

```text
K_L(initial) = n 2^(n-1),  L >= 1.
```

At a sorted output, a baseline with `z` zeros needs respectively
`z,z-1,...,1` extra ones to activate its zero wires. The order-`h`
hypergraph is the complete `h`-uniform hypergraph on the `z` missing inputs;
its transversal number is `z-h+1`. Consequently

```text
K_L(sorted) = sum_z binom(n,z) sum_(h=1)^min(L,z) (z-h+1).
K_n(sorted) / K_n(initial) = (n+3)/4.
```

The scale `L=1` is exactly conserved: its transversal is the routing-group
size, whose sum is the number of missing inputs at every baseline. Mixing
this conserved quantity into a potential can lower its apparent growth
rate while diluting its endpoint amplification. Both quantities must be
tracked. For fixed `L`, endpoint amplification is at most `L`, so no fixed
list of fixed cutoffs supplies a logarithmic lower bound by this argument.

## Finite feasibility screen

`kahale_activation_scales.py` uses complete reachable Boolean-prefix
catalogues, all nonempty parallel matchings, and every cutoff `1,...,n`.
It independently checks hypergraph AND/OR transport, full hypergraph
duality with extremal-input certificates, and the sorted endpoint formula.
It computes exact rational worst layer ratios for each scale.

It also screens nonnegative combinations `sum_L w_L K_L`, normalizing
`sum w_L=1`. For each candidate rate `rho`, a numerical linear program
maximizes endpoint amplification subject to every enumerated layer obeying
`Phi(next) <= rho Phi(before)`. Its residual is saved; LP output is not
an exact proof, and the inequalities concern only the enumerated width.
The quantity `log(amplification)/log(rho)` is a finite depth estimate,
**not an asymptotic coefficient**.

On four wires (261 states), 6,264 baseline comparator updates pass. The
initial vector is `(32,32,32,32)` and the sorted vector `(32,49,55,56)`.
Worst layer ratios are `(1,5/4,5/4,51/40)`.
At rate `1.18`, the best screened combination has endpoint amplification
about `1.4986` and finite depth estimate `2.4441`. It uses scales 1, 2,
and 3, with no scale-4 contribution. Thus this finite fit provides no
evidence that the growing-order endpoint can retain a sufficiently low rate.

On five wires (43,337 states), 3,466,960 baseline comparator updates pass.
The initial vector is `(80,80,80,80,80)` and the sorted vector
`(80,129,152,159,160)`. Worst layer ratios are
`(1,6/5,57/46,5/4,141/112)`. At rate `1.18`, the numerical optimum has
weights approximately `(0.193529,0.266732,0,0,0.539740)`, amplification
`1.703113`, and finite depth estimate `3.216986`. Here a full-order term
does survive the fit. This is worth testing at larger scales, but the
weights depend on width and do not establish a uniform rate or endpoint
amplification of order `n`.

The adjacent-baseline identity passes 1,692 checks on distinct four-wire
functions and 121,360 on distinct five-wire functions.

For comparison, a uniform rate bound on full conditional certificate cost
would give an asymptotic coefficient `1/log_2(rho)`. Coefficient 4 requires
`rho <= 2^(1/4) = 1.189207...`; the exact four-wire `51/40` gadget rules
that bound out for this unmodified potential. Disjoint copies preserve
its ratio at arbitrarily large widths divisible by four. This rules out
that particular one-layer bound, not all amortized or structural methods.

## Stronger large-width obstruction: aligned sorted blocks

There is a more severe obstruction than the four-wire gadget. Sort two
disjoint blocks of `m` inputs, then compare corresponding output positions
in a single layer. This is a realizable prefix followed by a valid parallel
layer, whether or not that last layer completes sorting.

In a sorted block, the wire at position `j-1` has threshold `t=m-j+1` and
every zero baseline has conditional zero-certificate size `j`. Let

```text
F_j = sum_(a=0)^(m-j) binom(m,a).
```

For two corresponding wires at a baseline where both are zero, the AND
certificate has size `j`: forcing either child to zero suffices, and
independent blocks cannot do better. The OR certificate has size `2j`:
both children must be forced to zero. The layer therefore increases
the cost by `j` on each of the `F_j^2` joint zero baselines. On a mixed
baseline it preserves the cost; on a joint one baseline it contributes zero.
The exact layer ratio for full conditional zero-certificate cost is

```text
1 + [sum_(j=1)^m j F_j^2] / [m(m+3) 2^(2m-2)].
```

This tends to `3/2`. To see this, put `p_j=F_j/2^m`. For every fixed
`delta>0`, the variance bound for `Bin(m,1/2)` gives `p_j -> 1` uniformly
for `j <= (1/2-delta)m`, and `p_j -> 0` uniformly for
`j >= (1/2+delta)m`. The intervening band's contribution to
`m^(-2) sum j p_j^2` is `O(delta)`. Taking `m` large and then `delta`
small gives limit `1/8`; the denominator divided by `4^m m^2` tends
to `1/4`. Thus the extra ratio tends to `1/2`.

The script `kahale_sorted_block_activation.py` computes exact integer
counts and independently sums all input-weight cases for block sizes up
to 8. Observed ratios for `m=2,8,32,128` are respectively
`1.275, 1.339325, 1.406330, 1.450941`.
The asymptotic argument is derived, not Lean checked.

Consequently any universal one-layer growth cap for the full unmodified
certificate potential must be at least `1.5`. Using just this cap and its
linear endpoint amplification could yield at most
`1/log_2(1.5) = 1.709511...`, below the existing lower bound. This is a
barrier to that proof scheme, not an upper bound on sorting-network depth
or on stronger multiscale methods. It leaves open charging the substantial
preparation of the sorted blocks.

## What to try next

The missing object is an amortized charge for **shared hitting obligations**.
Counting transversals separately throws away the overlap between adjacent
baselines: the same input set may cover many obligations, and an AND union
may have been paid for by existing child certificates. The baseline-shift
identity makes these shared obligations explicit.

A concrete next screen should distinguish two states with the same scale
costs but different overlap among their near-minimum hitting sets. Retain
families of hitting sets at adjacent baselines, rather than just their
minimum cardinalities, and look for a transport or charging inequality
that accounts for preparing the four-wire growth spike and median/mirror
prefixes, and now the aligned sorted-block family. A successful charge must control initial and sorted values as
well as every actual parallel layer; finite fitted weights alone do not
provide it. No such inequality is established in this note.

## Reproduction

From the repository root:

```text
python -B lower-bound/experiments/scripts/kahale_activation_scales.py --wires 4 --output docs/kahale-activation-scales-four-results.json
python -B lower-bound/experiments/scripts/kahale_activation_scales.py --wires 5 --output docs/kahale-activation-scales-five-results.json
python -B lower-bound/experiments/scripts/kahale_sorted_block_activation.py --output docs/kahale-sorted-block-activation-results.json
```

The LP uses locally installed NumPy and SciPy. No Lean changes or builds
are required for this investigation.
