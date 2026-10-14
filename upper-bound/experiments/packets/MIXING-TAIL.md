# Rounded matching-cycle bulk and tail interface

Status: hand-derived conditional lemma plus a finite floating-point screen.
No explicit unbounded matching family or sorting-network improvement is
proved.

## A uniform per-packet estimate from a spectral cycle

Let `c` equal-size sorted packets be mixed by `s` fixed perfect matchings.
On each matched pair, merge and deal maps Boolean threshold counts by
`(x,y) -> (ceil((x+y)/2), floor((x+y)/2))`. Write `A_t` for exact real
averaging on matching `t`, `P=A_s...A_1`, and assume

```text
||P z||_2 <= rho ||z||_2   for every zero-sum z.
```

For one threshold, let `x_j` be the input count in packet `j`, with
`H=sum_j x_j`. One rounded matching is `x' = A_t x + e_t`: on each pair the
rounding errors are `(+1/2,-1/2)` or `(0,0)`. Thus `sum e_t=0`,
`||e_t||_2 <= sqrt(c)/2`, and `||e_t||_infinity <= 1/2`. Expanding all `s`
rounds gives

```text
x_out = P*x + sum_(t=1..s) A_s...A_(t+1)*e_t.
```

Each averaging matrix is doubly stochastic and contracts `L2` and `Linf`.
Therefore, with `z=x-(H/c)1`,

```text
||x_out-(H/c)1||_2 <= rho*||z||_2 + s*sqrt(c)/2,
max_j |x_out[j]-H/c| <= rho*H + s/2.
```

For the second inequality, `P` is doubly stochastic and every entry differs
from `1/c` by at most `rho`: apply the spectral hypothesis to
`e_j-(1/c)1`, whose norm is at most one. Each propagated rounding-error
coordinate is at most `1/2`. The bound applies independently to every
Boolean threshold and therefore to both orientations of rank error. It
handles the singleton obstruction by allowing an explicit additive fringe
of `s/2` per packet; it does not claim a singleton spreads.

For `0<=x_j<=m`, `||z||_2^2 <= mH`. Since `sum z=0`, the one-sided bulk
leakage satisfies

```text
sum_j (x_out[j]-H/c)_+
  <= (sqrt(c)/2)*||x_out-(H/c)1||_2
  <= (rho/2)*sqrt(c*m*H) + s*c/4.
```

This gives a two-regime interface: square-root bulk control for larger
cohorts, and a per-packet `rho*H+s/2` upper tail for small cohorts. A
scheduler can use it only if it explicitly carries or repairs the `s/2`
fringe at every packet boundary and accounts for it across all active rank
thresholds.

## Finite cycle screen

`matching_cycle_screen.py` samples independent random perfect matchings and
computes the top singular value of `P-J/c` in binary64. With ten trials per
size, all sampled 26-round products for `c=16,32,64,128,256,512,1024` had
measured `rho < 0.0011`; the largest observed median was `0.0009668` at
`c=1024`. The
fixed reproducible PCG64 seeds and measured norms are saved in
`matching-cycle-screen.json`. Thirty rounds measured still smaller norms.

These measurements are an encouraging finite feasibility screen only. They
are not outward-rounded spectral certificates and do not give a family for
unbounded `c`. In particular, a random sample for each finite size cannot be
substituted for the uniform explicit matching family in the ticket.

## Depth gate and remaining scheduler test

For packet length `m=2^12`, the merge-and-deal operation costs 13 layers.
Twenty-six matching rounds cost 338 layers. If the 64-fragment receive pattern
can be implemented with six balanced merge levels, the previously derived
57-layer reassembly cost gives 395 total layers, or coefficient 197.5 at two
bits of scale per cycle. This leaves only 2.5 coefficient units before any
other work. The additive 13-key-per-packet fringe from the rounded cycle is
not a comparator-depth charge by itself, but may force extra repair or larger
fragments; that cost is not included in 197.5.

The next decisive result is either an explicit unbounded matching family with
a certified `rho` strong enough for the coupled cohort invariant, plus a
complete ordinary/frontier port-flow proof charging that fringe and all
reassembly, or an obstruction showing those costs exceed the gate. The
existing 26-round figure and this finite screen do not establish either.
