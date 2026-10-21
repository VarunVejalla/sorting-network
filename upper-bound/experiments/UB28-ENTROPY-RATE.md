# UB-28 local-transfer entropy-rate route

Status: research sketch, not a bound. The exact backward edge transfer in
[`ub28-local-edge-transfer.py`](ub28-local-edge-transfer.py) gives a bounded
number of count coordinates at every scale. This note records the natural
large-deviation objective for turning those transfers into an all-size first
moment proof.

Use 70 independent uniform matching rounds at every scale `h>=8`, in both
offset passes, and exact complete-bipartite splitters below width 8. For
`n=2^L` this costs at most
`140 * max(L-3,0) + 14` layers, so closing the probability gate would give
`limsup D(n)/log2(n) <= 140`. Random matchings at the finitely many small
widths do not need a separate universal-halver property in this first-moment
route.

## One matching round

For two blocks of width `h`, let `a` be the left one-count and `c=a+b` the
conserved total. After one uniform perfect matching, the new left count `x`
has law

```text
P(x | a,c) = C(c-a,x) C(h-c+a,a-x) / C(h,a).
```

For normalized densities `alpha=a/h`, `gamma=c/h`, `xi=x/h`, Stirling's
formula gives the log-probability rate

```text
J(alpha,gamma,xi) =
  (gamma-alpha) H(xi/(gamma-alpha))
  + (1-gamma+alpha) H((alpha-xi)/(1-gamma+alpha))
  - H(alpha),
```

where `H(t)=-t log t-(1-t)log(1-t)`, with continuous endpoint values and
the feasible range
`max(0,gamma-1) <= xi <= min(alpha,gamma-alpha)`.
For `d` independent matching rounds, the fixed-`d` log-probability rate from
initial density `alpha_0` to terminal density `alpha_d` is the maximum of
`sum_{t<d} J(alpha_t,gamma,alpha_(t+1))` over feasible intermediate
densities. All rates here are nonpositive. The maximum, rather than a sum,
appears because the number of integer paths is polynomial in `h` for fixed
`d`.

## One block split

When a width-`2h` block with density `rho` is split into two width-`h` blocks,
the left child density `u` has probability

```text
C(h,hu) C(h,h(2rho-u)) / C(2h,2h rho),
```

whose log-probability divided by `h` tends to
`H(u)+H(2rho-u)-2H(rho)`.

## Full local path objective

For a fixed output edge, the exact backward support has at most six count
coordinates at each scale. A trajectory consists only of count variables in
this edge's backward dependency cone; it does not sum over unrelated block
counts. It consists of these local counts at each split and each matching
round, ending in one of the finite width-4
profiles that triggers the terminal bad-edge predicate after the exact
width-4/2/1 suffix. Its log probability is the sum of the binomial
initial-count rate
`(H(alpha)+H(beta)-2 log 2)/2` per input wire for the two top-level blocks,
the matching-round rates `J`,
and the split rates above, weighted by each block width divided by `n`.
There are only `O(d log n)` trajectory coordinates and at most
`exp(O(d log^2 n))` integer trajectories, subexponential in `n` for fixed
`d`. Let `M_d` be the supremum, over feasible bad-edge trajectories and edge
phases, of their total normalized log-probability (initial, split, and
matching terms weighted by block width divided by `n`). Define `I_d = -M_d`,
so `I_d` is a nonnegative cost. A strict rate gap `I_d > log 2`, uniform
over output-edge phase and boundary trajectories, would imply

```text
E[number of failing inputs] <= n * exp(-(I_d-log 2)n + o(n)) < 1
```

for all sufficiently large powers of two. The zero-one principle and wire
restriction would then give the limsup bound with coefficient `2d`.

## Proof gate

The required rate is the minimum cost `I_d` over all feasible local
trajectories leading to a bad terminal edge, including every edge phase and
boundary case. Exact local transfer at `n=64,d=70` gives `P[bad]=0` for
edges 0 and 1, `1.21e-60` for edge 14, and `1.85e-62` for edge 30. These
sampled phases have finite-size rates above `2.2`, but do not establish the
limiting infimum or cover all phases. The missing gate is
an explicit finite-state (or otherwise uniform) optimization covering every
edge phase and boundary trajectory, together with a uniform `o(n)` bound for
finite-width entropy errors and trajectory counts. The next research step is
a certified discretized optimization of that recurrence. No coefficient
improvement is claimed until this gate proves `I_70 > log 2`.

To probe scaling beyond the exact Fraction table, the experimental
[`ub28-local-edge-float.py`](ub28-local-edge-float.py) implements the same
local transfer as dense NumPy arrays, forms each multi-round matching kernel
by a power of its one-round hypergeometric kernel, and rescales after every
operator while accumulating the log scale. It agrees with the exact transfer
to displayed precision at `n=32` and `n=64`. At `n=128,d=70`, central edge 62
has `-log(P[bad])/n = 1.16394`, still above `log 2`; this is numerical
finite-size evidence only. The `n=256` central-edge table reaches six count
coordinates at width 32 (`33^6` entries), so dense arrays exceed practical
memory. A tensor/low-rank or certified rate recurrence is needed to get past
that bottleneck.
