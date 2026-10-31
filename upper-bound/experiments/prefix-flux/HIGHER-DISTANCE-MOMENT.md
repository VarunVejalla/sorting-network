# Higher distance moments for the D2 prefix transfer

2026-10-22. Exact potential identities and finite oracle diagnostics; no
fixed-provider theorem or sorting bound is claimed.

## Potential and terminal use

Lean now checks `prefixIntervalMass_signed_error_eq_endpoint_defects` and
`sum_weighted_prefix_increments_by_parts` in `D2RankAlignment.lean`. Together
they express each signed rank-port error as a difference of endpoint prefix
defects and give the exact summation-by-parts identity for weighting those
errors by spatial distance. `D2WeightedPortDefect.lean` composes them into
`weighted_port_error_by_parts`, for an arbitrary monotone rank partition and
arbitrary rational port weights. The identity is only an algebraic interface:
the actual D2 schedule still needs an all-depth bound on the resulting
weighted prefix defects.

For a Boolean word `w` with `q` zeros, define for integer `s>=1`

```text
M_s(w) = sum_{x<q, w[x]=1} (q-x)^s
       + sum_{x>=q, w[x]=0} (x-q)^s.
```

This is a distance moment of misplaced wires. `M_1` is exactly the inversion
count. Every ascending comparator is nonincreasing for every `M_s`: if it
swaps `1,0` within the left side, the wrong one moves closer to `q`; within
the right side, the wrong zero moves closer to `q`; across `q`, it corrects
both errors. This monotonicity alone gives no strict contraction.

If `M_s(w) < B^s`, then every misplaced wire is at distance `<B` from `q`.
The fixed chunk/seam cleanup in `INVERSION-LOCALIZATION-GATE.md` therefore
applies with dirty width at most `2B+O(1)`. For the `(3,3,2)` prefix schedule
with cost coefficient `273`, it would suffice to prove
`M_s(w) <= N^(s*theta)` for some `theta < 27/301`; the resulting cleanup
coefficient is at most `(273+theta)/(1-theta) < 300`. This replaces the
ordinary inversion gate by a stronger weighted contraction target; it does
not yet prove that target.

## Exact weighted prefix-area identity

Let `F(r)=min(q,r)-Z(r)` for cuts `0<=r<=N`, as in `PROFILE-GATE.md`. For
`1<=r<N`, set

```text
lambda_s(r) = (q-r+1)^s - (q-r)^s,    r<=q,
              (r-q)^s - (r-q-1)^s,    r>q.
```

Then the exact identity is

```text
M_s(w) = sum_{r=1}^{N-1} lambda_s(r) * F(r).
```

Each misplaced one at `x<q` contributes `F(r)` at cuts `x<r<=q`; the
telescoping left weights sum to `(q-x)^s`. Each misplaced zero at `x>=q`
contributes at cuts `q<r<=x`; the right weights sum to `(x-q)^s`. For `s=1`,
all cut weights are one, recovering `sum_r F(r)=inv(w)`.

Now partition the static wires into ordered bags `B`, with local labels
`w_B(0)<...<w_B(a_B-1)`. Let `H_B` be the bag's zero count, `Y_B(j)` its
output zero-prefix count, and
`d_B(j)=min(H_B,j)-Y_B(j)`. Let `c_B(r)` count bag wires below cut `r`, and
define the bag-sorted alignment defect

```text
A(r) = min(q,r) - sum_B min(H_B,c_B(r)).
```

The pointwise identity `F(r)=A(r)+sum_B d_B(c_B(r))` gives the exact higher
moment decomposition

```text
M_s(w) = sum_r lambda_s(r) A(r)
       + sum_B sum_{j=1}^{a_B-1} Gamma_{B,s}(j) d_B(j),
Gamma_{B,s}(j) = sum_{r: c_B(r)=j} lambda_s(r).
```

The coefficient `Gamma` is the sum of the distance-gradient weights over
the global-cut gap between consecutive static wires of `B`. At `s=1` it is
exactly `w_B(j)-w_B(j-1)`, the gap weight already used in
`PROFILE-GATE.md`. Thus the same local defects support all integer moments;
higher `s` prices errors farther from the threshold more heavily.

The gap sum telescopes explicitly. For consecutive labels `a=w_B(j-1)` and
`b=w_B(j)`,

```text
Gamma = (q-a)^s-(q-b)^s,               b<=q;
        (b-q)^s-(a-q)^s,               a>=q;
        (q-a)^s+(b-q)^s,               a<q<b.
```

This is the exact coefficient to use when pricing a local defect at an
actual D2 static-wire gap; no sum over the ambient interval is needed.

The next-stage mass perturbation also has an exact signed form. If `H_C^0`
is the destination mass under perfectly sorted source bags and `H_C` its
actual mass, then

```text
H_C-H_C^0 = sum_{ports B->C} (d_B(u)-d_B(v)),
```

for source port ranks `[u,v)`. The change in the destination bag-sorted
moment is the oriented sum of `phi_s(w_C(j))` over ranks crossed between
`H_C^0` and `H_C`, where

```text
phi_s(x) = -(q-x)^s, x<q;
           (x-q)^s,  x>=q.
```

For `s=1`, `phi_1(x)=x-q`, recovering the signed linear mass-shift formula.
This identifies a concrete recurrence target: combine these signed port
shifts with the `Gamma_{B,s}`-weighted local tail defects, retaining the
actual D2 phase and static-wire cut geometry. No such all-profile transfer is
proved yet.

## Candidate replacement for a uniform per-node outsider budget

The usual local contract bounds every prefix defect separately,
`d_B(j) <= E_B`. Summing those independent maxima gives the coarse local
moment allowance
`sum_j Gamma_{B,s}(j) E_B`, as though the node could saturate every cut at
once. The more useful contract would bound the aggregate directly:

```text
sum_j Gamma_{B,s}(j) d_B(j) <= L_{B,s}(a_B,H_B,wire-order).
```

This can tolerate a larger maximum defect at a few cuts while controlling the
total weighted local error. The exact layer-cake form is

```text
sum_j Gamma_{B,s}(j) d_B(j)
  = sum_{h>=1} sum_{j: d_B(j)>=h} Gamma_{B,s}(j).
```

The pointwise budget `d_B(j)<=E_B` only yields the coarse bound
`E_B*sum_j Gamma_{B,s}(j)`, as if every cut could simultaneously attain its
worst allowance. A sharper common-provider theorem would directly control the
weighted sum (or its defect-level sets) for every sender profile, then use the
signed port-shift identity above to transfer it between stages. This is a
proposed replacement interface, not a proved provider theorem. The root-tail
LP diagnostics in `PROFILE-GATE.md` show that the current pointwise envelope
alone leaves about2.24% terminal error at depths4--5, even after denser
row-cut sampling; they do not rule out this aggregate contract or the fixed
network.

### Hybrid aggregate-plus-seam budget for actual D2 bags

For the inversion moment `s=1`, the local weight is the gap between
consecutive static labels, `Gamma_B(j)=w_B(j)-w_B(j-1)`. In the actual D2
state, `bag_intervals` represents a bag as one parent interval with the
occupied child intervals removed. There are at most eight children, and each
child subtree occupies one interval or is empty. Therefore every bag is a
union of at most nine contiguous wire runs. The gaps `Gamma_B(j)` equal1
inside those runs and exceed1 at at most eight seam ranks. Thus the exact local
weighted charge splits as

```text
sum_j Gamma_B(j) d_B(j)
  = inv(local output on B)
    + sum_{seam j} (Gamma_B(j)-1) d_B(j).
```

This suggests a more tolerant interface than a pointwise outsider allowance
at every local rank: bound the total local inversion count, while retaining
pointwise rank-tail bounds only at the at most eight D2 seams. A useful
provider contract would be `inv_B <= L_B(H_B)` plus seam bounds
`d_B(j)<=E_{B,j}`; its weighted local contribution is then at most
`L_B + sum_seam (Gamma_B(j)-1)E_{B,j}`. This identity is exact for each
reachable static bag and the nine-run fact follows from the interval
construction, not from an input-dependent oracle trace.

The same sparse set of pointwise cuts also suffices for the mass recurrence.
An ordinary sender has eight child ports plus its two end up-ports, hence at
most nine internal port-boundary ranks. Every port's mass perturbation is
exactly `d_B(u)-d_B(v)` at its two endpoint ranks. Therefore a stage-level
hybrid API needs at most the union of eight static-run seams and nine port
boundaries per bag as pointwise defects, plus one aggregate bound
`sum_j d_B(j)=inv_B` for the rank positions between them. No other local rank
defect appears in either the weighted inversion identity or the exact port
mass-transfer identity. The overlap can reduce the count further. This is the
concrete form of relaxing the Chvatal budget: spend pointwise error only where
the D2 wiring changes destination or static-gap weight, and price the dense
interior by one aggregate inversion allowance.

The hybrid only addresses the weighted local-defect term. The global alignment
term `sum_r A_t(r)` in the inversion transfer remains unpriced, and the
two-scramble rate screen above says a random-core union bound for the aggregate
local inversion target may itself be too weak. Still, it gives a concrete
place to spend a more tolerant error budget: allocate it across aggregate
local inversions and the small, structurally forced set of seam ranks, then
test that budget against the actual active D2 levels.

`seam_budget_screen.py` propagates occurrence multiplicities through the
actual shared D2 flow and sums `a_B * sum_seam(Gamma_B(j)-1)` over all active
senders. At depths30 and100, scale8192, `(3,3,2)`, every active sender has at
most9 runs, and the complete-stage normalized coefficient is
`0.0131146569074` in both screens; stages2 and3 contribute
`0.00389099121094` and `0.00732421875`. If one provisionally uses the ragged
provider's relative local cut cap `17/4000`, this bounds the accumulated seam
term by `5.57373e-5*N^2` on those finite flows. This supports keeping seam
budgets separate from interior aggregate error, but the fixed-fraction bound
is not the subpolynomial terminal inversion target, and the alignment/local
inversion recurrence still must contract. The script checks exact integer
flow geometry at finite depths; it is not the required all-depth summability
proof.

## Shape-only aggregate screen

There is an immediate restriction on any realizable defect profile, independent
of the network: since `Y(j+1)-Y(j)` is either0 or1, `d(j)` is nondecreasing
for `j<=H` and nonincreasing for `j>=H`. I applied this unimodality to the
current integer row-boundary caps `E(j)` by replacing each cap on the rising
side with the minimum cap from `j` through `floor(H/n)`, and on the falling
side with the minimum cap from `floor(H/n)` through `j`. For `m=64` and `256`
rows, across column widths `n=16,256,4096`, this lowered the unweighted sum
of independent caps by only about2--3% at `H/a=1/3` and did not lower it at
`H/a=1/2`; at `H/a=1/8`, it gave about8--22%, depending on row count. This is
only a cap-envelope screen, not an attainable profile or a provider theorem.
Unimodality alone therefore looks too weak near the balanced sender profiles;
the useful aggregate budget must exploit stronger shared-profile constraints,
the actual 3-sort output, or how the defect is sampled by D2 port cuts.

An exact finite screen of the fixed core is in
`local_core_aggregate_screen.py`. For each fixed pair of row scrambles, it
enumerates every post-first-sort column-height vector and runs both remaining
column sorts exactly. With4 columns and8 rows (6,561 profiles), seeds0--2
gave maximum summed full-row defects4,6,8; the worst ratio over all masses of
this aggregate to the sum of the existing independent row-cut caps was
0.107--0.130. With4 columns and16 rows (83,521 profiles), the maxima were
10,8,12 and the ratios were0.046--0.064. These are fixed local cores valid
for every enumerated input in those small dimensions, unlike input-dependent
oracle traces. They suggest the common fixed network can have substantial
aggregate slack. The enumeration covers only full-row cuts, tiny column
counts, and each listed scramble pair; it neither proves a scalable scramble
choice nor prices the actual D2 port weights. The next proof target is a
uniform expectation/tail bound on the `Gamma`-weighted defect sum under the
two scrambles, followed by a union bound over sender states rather than over
every cut separately.

An additional `m=32,n=4` exhaustive run (`1,185,921` profiles, seed0) found
maximum aggregate defect13 at total height88, peak single-cut defect5, and
aggregate-to-pointwise-cap ratio0.0278. This continues the downward ratio
trend at larger row height for this one fixed scramble pair. It remains only
a four-column finite screen; the number of input profiles grows as
`(m+1)^n`, and no uniform tail or actual-scheduler guarantee follows.
The corrected exact MILP independently certifies the same maximum13 at
zero gap. Its unary balanced-square baseline variables are continuous rather
than binary; since total mass is integral and the baseline is piecewise linear
with integer breakpoints, this preserves the exact objective while reducing
unneeded integrality.

At `m=64,n=4`, the exact unary MILP has only 1,024 variables but does not
certify an optimum in 120 seconds: the strengthened model's area-19 incumbent
has relative gap6.03. The continuous relaxation solves immediately but
returns area2,048, far too weak to extrapolate the integral worst case. Thus
the current unary MILP is a poor tool for extending the exact maximum-profile
table beyond32 rows; a tighter formulation or a proof of a discrepancy bound
is needed.

## Exact two-round expected area bound

For an `m`-by-`n` rectangle, write `A` for the sum of local prefix defects at
all full-row cuts, including the zero endpoints. If the final column heights
are `C_1,...,C_n` and `H=sum C_j`, then

```text
A = 1/2 * (sum_j C_j^2 - min_{u_1+...+u_n=H, u_j integers} sum_j u_j^2).
```

At row `k`, the output tail is `sum_j (C_j-k)_+`; subtract the ideal tail
`(H-kn)_+` and sum over `k`. The minimum is attained by heights differing by
at most one. Thus the aggregate defect is a column-height dispersion, not a
sum of separately maximized cut errors.

Take two independent scrambles, each a uniform independent permutation of the
columns in every row, with a column sort after each. Start from any fixed
matrix and let `x_r` be its row counts. After the first scramble, each height
is `C_j=sum_r X_{rj}` with `E X_{rj}=x_r/n`, independently across rows. After
the second scramble, conditional on `C`, the row counts are
`x'_r=#{j:C_j>r}`. Applying the exact identity and variance formula to the
last column sort gives

```text
E[A_final | C]
 = 1/2 * (sum_r x'_r*(1-x'_r/n) - u*(1-u/n))
 <= 1/(2n) * sum_{j<k} |C_j-C_k|,
```

where `u=H mod n`. The identity
`sum_r x'_r*(n-x'_r)=sum_{j<k}|C_j-C_k|` counts pairs of columns separated by
each row cut. For each pair, `C_j-C_k` is a sum of independent centered row
contributions, with

```text
E[(C_j-C_k)^2]
 = sum_r 2*x_r*(n-x_r)/(n*(n-1))
 <= m*n/(2*(n-1)).
```

Cauchy-Schwarz proves the profile-uniform estimate

```text
E[A_final] <= 1/4 * sqrt(m*n*(n-1)/2).
```

There is a sharper absolute-moment estimate. For one row, the difference of
the two column indicators takes values `+1,-1` with probability `alpha/2`
each, and0 otherwise, where
`alpha=2*x_r*(n-x_r)/(n*(n-1))`. If `S` is a symmetric integer-valued sum
of the other rows, then

```text
E|S+Z_alpha| = E|S| + alpha*Pr[S=0],
```

so `E|sum_r Z_r|` is increasing in each `alpha_r`. The finite-width maximum
is `beta_n=2*floor(n^2/4)/(n*(n-1))`, attained by taking every row population
as close to `n/2` as possible. Let `L_m(beta)` be the exact expected absolute
value of a sum of `m` independent increments with probabilities
`Pr[+1]=Pr[-1]=beta/2`, `Pr[0]=1-beta`. Substitution into the pair sum gives

```text
E[A_final] <= (n-1)*L_m(beta_n)/4.
```

As `n` grows, `beta_n` tends to1/2. At that limit the lazy walk is the
difference of two independent `Binomial(m,1/2)` variables, so
`L_m(1/2)=m*binom(2m,m)/4^m`. The limiting area fraction is therefore
`binom(2m,m)/(4*4^m)`, asymptotic to `1/(4*sqrt(pi*m))`. At `m=4096` it is
0.0022038, compared with0.002762 from the looser variance-only estimate.
Since each one-step change of `d(j)` has magnitude at most1, any partial-row cut satisfies
`d(j) <= A_final+n`; the same area event therefore controls every local cut
with an additive `n` allowance. As every full-row defect is nonnegative, each
one is at most their sum `A_final`. Consequently the actual weighted local
term obeys the deterministic bound

```text
sum_j Gamma_{B,s}(j) d_B(j)
  <= (A_final+n) * sum_j Gamma_{B,s}(j).
```

The coefficient sum is the potential-gradient weight across the sender's
static-wire span (exactly its span for `s=1`). Thus the expectation estimate
already prices a conservative `Gamma`-weighted outsider budget, although it
does not exploit where the large weights occur.

For `m=4096`, double-precision evaluation of the exact lazy-walk recurrence
gives expected-area fractions0.002187,0.002199,0.002204 at `n=64,256,4096`;
adding the partial-row allowance `1/m` gives0.002431,0.002444,0.002448.
These are expectation bounds for each fixed input profile under random
scrambles, not simultaneous all-input bounds.

This is an exact expectation bound for random scrambles, uniform in the input
profile; it is **not** a fixed-scramble all-input guarantee. The missing step
is a tail/concentration estimate strong enough to select one pair of scrambles
that satisfies the aggregate budget for every sender input, while paying for
the number of sender states and actual `Gamma` weights. This is the most
promising replacement so far for independent Chvatal-style per-cut outsider
allowances: it gives a small aggregate mean, but no probability or all-depth
D2 transfer has yet been established.

### Mass-sensitive refinement

The same calculation gives a useful bound that vanishes for pure senders.
Let `H=sum_r x_r` be the sender's zero count and
`h=min(H,m*n-H)` its minority mass. By Cauchy/Jensen,

```text
sum_r x_r*(n-x_r) <= n*h - h^2/m
E[(C_j-C_k)^2] <= 2*h*(1-h/(m*n))/(n-1).
```

Substituting this into the pairwise absolute-difference bound yields

```text
E[A_final] <= sqrt((n-1)*h*(1-h/(m*n))/8).
```

This is profile-uniform at each fixed mass `H`, equals0 at pure profiles, and
recovers the previous `O(n*sqrt(m))` bound at balanced mass. For rectangular
senders with common row height `m`, sizes `a_B=m*n_B`, and minority masses
`h_B`, linearity of expectation and Cauchy give the stage aggregate estimate

```text
E[sum_B A_B] <= sqrt((N/m) * (sum_B h_B) / 8),
```

using `sum_B a_B=N` and dropping the factor `1-h_B/a_B`. The expression
becomes sublinear when the total minority mass over active senders is
sublinear. This is the promising bridge to a shrinking mixed-sender set, but
it still averages over scrambles, assumes exact rectangular layouts, and does
not bound `sum_B h_B` from the global inversion/rank profile. A fixed network
must satisfy all reachable sender profiles simultaneously; no such provider
or D2 recurrence is proved here.

To relate `sum_B h_B` to the global inversion state, let `P_B` count the
static labels of `B` below `q`, and let `W_t` be the total number of globally
misplaced bits. Since `H -> min(H,a-H)` is1-Lipschitz,

```text
sum_B h_B <= sum_B min(P_B,a_B-P_B) + sum_B |H_B-P_B|
           <= C_t(q) + W_t
           <= C_t(q) + 2*sqrt(Inv(w_t)),
```

where `C_t(q)=sum_B min(P_B,a_B-P_B)` is a purely geometric threshold-crossing
mass. The second inequality uses `sum_B |H_B-P_B|<=W_t`; the last follows
because if there are `u` misplaced ones left of `q`, there are also `u`
misplaced zeros right of `q`, and these force at least `u^2` inversions. In
the rectangular model, this gives the candidate one-stage expected-area
bound
`E[sum_B A_B] <= sqrt((N/m)*(C_t(q)+2*sqrt(Inv(w_t)))/8)`.

The exponent check is unfavorable if this is used as the only local-error
estimate. Even setting the geometric crossing term `C_t(q)` to zero, a target
`Inv(w_t)<=N^theta` yields only
`E[sum_B A_B]=O(N^(1/2+theta/4))` for fixed row height `m`. At the 273-layer
cleanup gate `theta=27/301`, this exponent is about `0.52243`, far above the
required `0.08970`; the 292.5-layer gate is similarly about `0.50623` versus
`0.02492`. This does not show that the actual local error is that large, but
it shows that this Jensen/Cauchy expectation bound cannot close the terminal
gate, even if the crossing term vanishes. A useful tolerant-budget theorem
must capture contraction/correlation beyond this first-moment estimate (and
still select one fixed provider for all sender states).

`mass_sensitive_budget.py` computes `C_t(q)` in the actual finite `(3,3,2)`
flow at `q=floor(N/3)`. At both depths30 and100, the normalized sequence is
identical: `C_0/N=1/3`, `C_1/N=1/24`, `C_2/N=0.00642904`, and the sum over all
active stages is `0.39203637`; excluding the first two stages, the sum is
`0.01703637`. This confirms strong geometric decay of the static crossing
term after startup, but it remains a finite audit. Moreover, even if `C_t`
were proved all-depth, its positive early-stage multiples of `N` and the
square-root dependence on `Inv` do not by themselves yield the required
`N^theta` terminal inversion. The global recurrence needs an exact startup
contract and a stronger contraction after those early stages.

The decay has a short candidate formulation: at depths12,30,100 every
available three-stage ratio satisfies
`C_(t+3)/C_t <= 0.126832 < 1/7`, with the maximum at `t=1`; the finite
`C_t/N` sequences agree through the initial phases and their complete sums
agree to the displayed precision. Proving `C_(t+3)<=C_t/7` directly from the
rounded D2 state recurrence would give an all-depth geometric charge for this
structural term. That lemma is not proved, and it controls only `C_t`, not the
actual sender minority mass or the local-provider tail event.

There is a route to avoid proving the `C_t` recurrence directly. At each
active level there is at most one sender bag whose native parent interval
contains `q`, and `min(P_B,a_B-P_B)<=a_B/2`. If every reachable sender
allocation satisfies `a_B <= K*Par.alloc(d,level,t)`, then

```text
C_t(q) <= (K/2) * S_t,
S_t = sum_{active levels i} Par.alloc(d,i,t).
```

The explicit schedule sum satisfies
`S_(t+3)/S_t <= 4159/32768 < 1/7` at every tested stage for depths30 and100.
Across all reachable sender types in those finite flows, the largest ratio
`actual allocation / Par.alloc` is `16/15` (at stage3, level3), with no
positive actual allocation over a zero formula cap; this checked 217,470
distinct types at depth100. The existing conditional `279/256` result bounds
`actual allocation / cap`, not `actual allocation / Par.alloc`, so it cannot
be substituted directly here. One must first derive a uniform role-by-role
comparison from that cap to `Par.alloc`; any finite constant `K` would suffice
for geometric decay. The finite maximum suggests `K=16/15`, but the needed
all-depth domination remains unproved. The explicit-sum inequality has the
following short paper derivation (not yet Lean-checked).

For the `(3,3,2)` schedule write
`c_(i,t)=N*8^i*4^(-t)/16`, `Q=4096`, and
`S_t=sum_{i active at t} Par.alloc(d,i,t)`. For `t>=2` the active levels are
the parity class between `alpha_t` and `omega_t`; their allocation terms are
`c_(alpha,t)` at the lower endpoint, `c_(i,t)*(1-1/Q)` in the interior, and
`N/8^omega-c_(omega,t)/Q` at the upper endpoint. (When `alpha=omega`, the
lower-endpoint formula applies.) The rounded schedule formulas give
`omega_(t+3)=omega_t+1` and
`alpha_(t+3)-alpha_t` in `{-1,1,3}`. If the difference is1, shifting every
active level by1 multiplies each allocation term by1/8, so
`S_(t+3)=S_t/8`. If it is3, the old lower term disappears; the newly exposed
lower term comes from an old interior level two higher. Since
`c_(i+2,t)=64*c_(i,t)`, the exact correction is
`S_(t+3)=S_t/8-(63/512)*c_(alpha,t) <= S_t/8`.
The `-1` case can occur only with `alpha_t=1`, `alpha_(t+3)=0`: the new lower
term contributes `c_(alpha,t)/512`, while the shifted old lower term loses
`c_(alpha,t)/(8Q)`. Hence
`S_(t+3)=S_t/8+(63/32768)*c_(alpha,t)`.
Because `c_(alpha,t)` is a term of `S_t`, this is at most
`(4159/32768)*S_t`. The startup values are
`S_0=N`, `S_3=79N/8192`, `S_1=N/8`, and
`S_4=4159N/262144`, so the same bound holds from `t=0,1`. For the recurrence,
define the *truncated preterminal* sum by `S_t=0` whenever `t>=t_f`, and
otherwise by the displayed sum over active levels. Claim the three-case
recurrence only when `t+3<t_f`; the terminal transition into `t_f` is a
separate boundary check because the flow simulator still treats `t_f` as
active. For example, at depth30 the transition `73 -> 76` has old frontier
gap2, outside the `+3` case assumptions, although its exact ratio `512/4159`
is still below the target. The other schedule side conditions in the `+3`
case are that the new active interval is nonempty (so
`omega_t-alpha_t>=4`) and that all listed allocation terms are nonnegative;
these follow directly from the preterminal frontier and sender formulas.

`mass_sensitive_budget.py --audit-schedule-allocation` checks these exact
rational identities for every applicable `(d,t)` through `d=30`, alongside
the reachable-state allocation comparison. This supports the algebra and
identifies the short Lean target, but the all-depth sender-allocation
domination `a_B<=K*Par.alloc(d,level,t)` remains an unproved bridge from the
recursive D2 state to the closed schedule formula.

### Deeper finite audit (2026-10-24)

Extended `mass_sensitive_budget.py --audit-schedule-allocation` to depth200
(scale8192, threshold1/3). The exact schedule-cap sum still has maximum
three-step ratio `4159/32768 = 0.126922607422` (at startup stage1), and the
actual crossing mass has maximum ratio `0.126831054688` for
`C_(t+3)/C_t`. Across 1,745,581 reachable sender types there are no positive
allocations over zero formula caps, and the largest actual/formula allocation
ratio remains exactly `16/15`, at `(t,i)=(3,3)`. All three `alpha`
displacement cases occur (145, 291, and 145 instances for `-1,1,3`). This
confirms the finite audit at a substantially deeper range; it is still not
the required all-depth domination theorem, so `K=16/15` remains conjectural.
The run completed but peaked near 4.5 GB, so depth200 is a poor routine
regression size.

### What the existing `279/256` factor does and does not give

It cannot simply be divided by the schedule allocation uniformly. At the
active bottom boundary `i=omega_t`, the exact residue classes are

| `t mod 3` | role | `cap/native` | `Par.alloc/native` | consequence from actual `a<=native` |
|---|---|---:|---:|---:|
| 0 | `botDesc` | 256 | 15/16 | `a/Par.alloc <= 16/15` |
| 1 | `botRise` | 1 | 4095/4096 | `a/Par.alloc <= 4096/4095` |
| 2 | `botRise` | 16 | 255/256 | `a/Par.alloc <= 256/255` |

These follow from `omega(3j)=j+2`, `omega(3j+1)=j+1`,
`omega(3j+2)=j+2`, and `Par.alloc(native endpoint)=native-cap/4096`;
the actual-native bound is already available from `d2FlowTreeInv`.
Thus the bottom endpoint is not the obstruction to a finite all-depth `K`.
For interior levels, `Par.alloc=(4095/4096)cap`, so an applicable
`a/cap<=279/256` would give `a/Par.alloc<=4464/4095`. The two-step
`279/256` algebra is conditional on its role-specific reserve hypotheses and
does not cover `topDesc`; the top-descending sender allocation still needs its
own bound. Consequently neither the finite `16/15` observation nor the
conditional `279/256` lemma alone proves the required all-depth domination.
One top-descending subcase is now isolated by the kernel-checked generic
transition lemma `d2FlowStage_topDesc_inactive_topRise_topDesc_allocation` in
`D2ScheduleReserve.lean`: if the sender's children were reset to zero by a
top-descending stage, the parent is inactive next, and all eight children are
`topRise` then, the sender allocation at the next snapshot is exactly eight
times the child quota. This matches the observed schedule pattern
`(alpha_t-alpha_(t-2), alpha_(t-1)-alpha_t)=(0,+1)`, where the child quota is
expected to be `c/8`. The schedule classification is now also kernel checked
as `alpha_topDesc_two_step_patterns`: every top-descending visit has exactly
one of three predecessor patterns, `(0,+1)`, `(0,-1)`, or `(2,-1)`. The fourth
arithmetic combination is impossible because it would make the frontier jump
three levels in one step, contradicting the adjacent-step bound. An exact
formula sweep through depth2000 agrees (1,989,015, 498,500, and 1,492,509
visits, respectively), though the proof comes from the Lean schedule lemma,
not that finite sweep. The `(0,-1)` and `(2,-1)` branches have ordinary
intermediate children and remain open. The focused next task is to prove their
allocation transfer, show the reset branch's child quota is exactly `c/8`,
verify the ordinary-role reserve hypotheses uniformly, and combine the cases
with the schedule-sum recurrence.

### Role-resolved finite gate

`d2_topdesc_allocation_screen.py` separates the actual top-descending sender
allocations by those three predecessor patterns. At depths20,30,40,100, the
`(0,+1)` and `(0,-1)` branches never exceed `Par.alloc`; the `(2,-1)` branch
has the same exact maximum `2093/2048` at all four depths (for example,
`t=45`, level5, allocation2093 versus scheduled2048 at depth30). Thus the
common factor `279/256` would cover all three frontier histories if proved.
These are finite fixed-flow checks only; they do not establish that factor or
the global allocation domination theorem.

For the hard `(2,-1)` history, the direct proof target can be sharpened. Let
`c=Par.alloc(d,i,t)` at the current top-descending level. The capacity ratios
are `cap(i,t-2)=16c` and `cap(i+1,t-1)=32c`. If the `mid` update at `(i,t-2)`
leaves aggregate child deficit at most its old deficit plus its quota, the
parent-deficit cap `G<=23/4096 cap(i,t-2)` and the `mid` quota `15/4096`
bound that aggregate by `(23+15)c/256=19c/128`. The eight `mid` child quotas
at `t-1` sum to `15c/16`. Since the top-descending parent resets its own
deficit to zero, these estimates give current allocation at most
`(19/128+15/16)c=139c/128=278c/256`. For `(0,-1)`, the previous `topRise`
quota is `c/16`, so the carry plus the same `15c/16` child-quota sum is at
most `g+c`, hence `279c/256` under `g<=23c/256`. The reset history `(0,+1)`
has exact allocation `c` when its eight child quotas are each `c/8`, using the
existing `d2FlowStage_topDesc_inactive_topRise_topDesc_allocation` lemma. The
two non-reset arithmetic cases are kernel-checked in `D2TopDescBound.lean`.
The missing work is to establish their schedule-role, reserve, and cut
premises from actual `D2FlowStage` transitions uniformly through all active
stages.

Focused Lean check passed on 2026-10-24 with
`lake env lean --root=../experiments/prefix-flux -o ../experiments/prefix-flux/D2ScheduleReserve.olean ../experiments/prefix-flux/D2ScheduleReserve.lean`
from `upper-bound/best`. The generated `.olean` is only a temporary check
artifact and is not part of the research source.

## Adversarial gate and uniformity obstacle

`local_core_adversary.py` fixes both scrambles, then uses exact incremental
updates to hill-climb the initial column heights against the final area. The
earlier coordinate-only search at `m=4096,n=64` found fractions around
0.0030--0.0034, but it missed exhaustive optima on some16-by-4 controls. The
script now also uses annealing, verified against exhaustive 8-by-4 and 16-by-4
cases (it matched3/4 tested seeds). At `m=4096,n=64`, 100,000 annealing steps
found area fraction0.006298; at `n=256`, 20,000 steps found0.004410 and
0.004306 for two seeds. The deterministic partial-row allowance `1/m`
increases the largest to0.006542, below the current per-cut target0.0085.
These remain heuristic adversarial searches, not a global maximum or
all-profile certificate; stronger optimization may find larger witnesses.

`local_core_milp.py` gives an exact global maximum for fixed scrambles by
encoding all three successive column-height profiles in unary. It matches the
exhaustive maxima on8-by-4 and16-by-4 controls (area4 and12 for the tested
seeds). It does not scale well in its current form: at64-by-16, HiGHS did not
close the MILP in60 seconds and returned an area incumbent35 with a very large
gap; the continuous relaxation permits area fraction32. This confirms the
small-model encoding but does not yet certify the target-row adversary.

The direct bounded-difference route to an all-profile theorem is too weak.
For `S(C)=sum_{j<k}|C_j-C_k|`, changing one transposition in one row scramble
changes `S` by at most `2(n-1)`. Exposing the `m` row permutations therefore
gives the safe tail

```text
Pr[S-E S >= t] <= exp(-t^2/(8*m*n*(n-1)^2)).
```

At `t=delta*n^2*sqrt(m)` this is at best `exp(-delta^2*n/8)`. A union bound
over all `(m+1)^n` initial column-height vectors would require
`delta > sqrt(8*log(m+1))`; for `m=4096` this exceeds8.1. Yet the area budget
0.0085, after the mean and partial-row allowance, permits only about
`delta<=0.70` even before reserving a second-stage tail. Similarly, exposing
the second scramble and using the `m`-Lipschitz change in area gives exponent
only `t^2/(2*m^3*n)`. Thus McDiarmid plus a union bound loses far too much.
The next useful proof would need a sharper concentration inequality for the
column-height dispersion (or a profile-compression argument that avoids
paying `(m+1)^n` separately), together with the actual `Gamma`-weighted
stage sum.

### Endpoint-profile rate screen (2026-10-23)

`endpoint_profile_rate_screen.py` checks an entropy-tilting hazard for the
endpoint input (half the columns full, half empty). It charges a first-scramble
intermediate type `nu` by `D(nu || Binomial(m,1/2))`, then computes a Chernoff
rate for the second-scramble output column height under an independent-column
approximation. The target aggregate fraction `0.0085` corresponds to centered
second moment `0.017m`. At `m=4096`, a symmetric two-binomial mixture shifted
by32 has input KL cost `0.16316`, second-round output variance `25.829`
(versus18.054 at the typical type), and independent-column second-round rate
`0.35347`. The combined rate is only `0.51663`, below the endpoint-profile
multiplicity exponent `ln 2 = 0.69315`. At shifts48 and64 the combined rates
rise to `0.77800` and `1.45190`.

This does **not** show a bad fixed scramble or failure of the aggregate
allowance. The actual second scramble fixes the number of selected columns in
each row; the independent-column calculation drops those constraints, which
can increase the true large-deviation rate. The screen does rule out relying
only on the typical intermediate profile and identifies a narrow mixture
family where a row-conditioned rate proof must recover at least `0.17652`
nats per column to beat the endpoint input-type entropy. The next calculation
is the same variational rate with all row marginals fixed, optimized over
intermediate types. Any resulting aggregate budget still has to be charged
through actual D2 sender levels and port weights.

`endpoint_profile_conditioned_screen.py` performs a first row-conditioned
stress test. Its second-round type is an equal mixture of two product laws
whose marginals are `p_r +/- k*p_r*(1-p_r)`; their average is exactly the
prescribed row-density vector, and `k` is chosen to make the column-height
second moment equal `0.017m`. The exact mixture-KL identity reduces the cost to
one product KL plus an expectation of `softplus(-Delta)`. A Lindeberg
replacement bound plus a closed-form Gaussian tail bound gives numerical
combined first-plus-second type-cost upper bounds `0.72168`, `0.65344`, and
`0.69848` nats per column for shifts24,32,40, respectively. The shift32
candidate is below `ln 2` by about `0.03971`.
This bound uses the exact sup norm `1/(6 sqrt(3))` of the third derivative of
`softplus(-x)` and explicit third absolute moments of the summands. The
computation respects all row marginals, unlike the previous independent-
column screen. The displayed decimal is not yet outward-rounded/certified, and
turning this candidate type into a no-fixed-core theorem requires a
second-moment or other existence argument over endpoint inputs. It does show
that a simple union bound over all endpoint inputs is unlikely to certify the
`0.0085` aggregate threshold even after fixing row marginals. This is evidence
to develop a weighted aggregate budget or a deliberately structured core, not
a proof that either route is necessary.

This is specifically a rate screen for the two-scramble rectangular local
core analyzed above; it is not a model of the ragged 13-bit provider or its
per-sender probability budgets. An independent 35-digit evaluation of the
shift32 quantities gives combined cost upper bound
`0.6534386701448258632851415`, leaving margin
`0.03970851041511944613209067` below `ln 2`.

The numerical bound follows from an explicit inequality. For
`Delta=mu+sum_i Y_i` with independent centered `Y_i`, replace each `Y_i` by
an independent Gaussian `G_i` of the same variance. Taylor expansion through
order two gives
`E h(Delta) <= E h(mu+sum_i G_i) + (sum_i E|Y_i|^3 + sum_i E|G_i|^3)/(36 sqrt(3))`,
since `||h'''||_infinity=1/(6 sqrt(3))` for `h(x)=log(1+exp(-x))`. For
`X~N(mu,sigma^2)`, the Gaussian expectation is bounded by the closed form
`exp(-mu+sigma^2/2) Phi((mu-sigma^2)/sigma) - mu Phi(-mu/sigma)`
`+ sigma phi(mu/sigma) + exp(mu+sigma^2/2) Phi((-mu-sigma^2)/sigma)`.
The bound comes from splitting at zero and using `h(x)<=exp(-x)` on the
positive half-line and `h(x)<=-x+exp(x)` on the negative half-line. Thus only
the numerical evaluation of explicit sums and Gaussian tails remains to be
outward-certified.

Scanning the shift32 Lindeberg upper bound in `epsilon` puts its crossing of
`ln 2` near `0.0087971`, about3.5% above `0.0085`. This is where this
particular cost upper bound stops proving a sub-`ln 2` type; it is not a
certified safe provider tolerance. It does not price the change in the global
D2 recurrence.

A follow-up grid scan optimizing over shifts in increments of2 moves that
crossing only slightly, to `epsilon=0.00881632` at shift34. At `epsilon=0.01`
the minimum sampled combined rate is `0.86278` at shift40, above `ln 2`.
Thus raising the **aggregate** area allowance from0.85% to about0.9% is a
plausible way to clear this endpoint entropy gate, and a1% allowance clears
the tested family with visible numerical margin. This supports testing a more
tolerant aggregate budget in the local provider. It does not justify raising
all pointwise outsider caps: the argument uses a weighted aggregate event,
and its price in the all-depth D2 profile recurrence remains unknown. The grid
and calculations are double precision, so these are search signals, not
outward-certified thresholds.

There is also a schedule-level affordability constraint. If every stage's
active sender bags partition the `N` wires and a uniform local contract only
gives `aggregate_defect(B) <= epsilon * |B|`, then summing it over the stage
allows `epsilon*N` local defect. Charging that additively for `T=Theta(log N)`
stages gives only an `O(epsilon*N*log N)` bound, far above the `N^theta`
terminal inversion gate for every `theta<1`. The finite D2 flow audit checks
the allocation sum `sum_B |B|=N` at every stage through depths30 and100. Thus
raising the local aggregate allowance by itself cannot close the route. The
provider must instead give an error term that contracts with the incoming
global potential, or the recurrence must show that only a shrinking total
allocation of mixed/near-threshold senders incurs this allowance. An LP knob
that merely adds a fixed per-sender area cap would test a contract that, by
itself, cannot close the inversion-gate argument.

For a direct finite gate, `aggregate_profile_union.py` computes the exact
transition law on column-height histograms for one random scramble/sort, then
sums two-round bad-event probabilities over every labeled initial profile.
The first runs give minimal strict area thresholds with union bound below1:
`m=2,n=6`: area3 (`3/12=0.25` of sender size, union bound `1/20`); and
`m=3,n=6`: area5 (`5/18`, union bound `1471/43200`). This is exact finite
probability accounting and directly certifies existence of a fixed pair only
at those thresholds. It is far above the0.0085 target, as expected at such
small row counts; it does not extrapolate to `m=4096`. Additional exact runs
give `m=4,n=6`: area7/24 (union `6493387/48600000`), `m=6,n=4`: area6/24
(union `4755313735/5159780352`), and `m=8,n=4`: area9/32 (union
`46741270361557/106993205379072`). The direct union bound over all labeled
profiles is very lossy in these finite rectangles. It needs profile
compression or a more structured all-input event to connect with the much
smaller defects seen by fixed-scramble coordinate ascent at `m=4096`.

## Finite screen

`sparse_probe.py` now records `M_1,M_2,M_3` on the same input-dependent
ordered oracle traces as its inversion screen. For `d=32,40,48,56,64`,
`root_eps=10^-20`, threshold `1/3`, row height8192, scale8192, and candidate
parameters `(3,3,2)`, the terminal root-normalized radii
`log_N(M_s)/s` decrease substantially with `s`:

| `d` | left `s=2` | left `s=3` | right `s=2` | right `s=3` |
|---:|---:|---:|---:|---:|
| 32 | .14554 | .13141 | .13529 | .12095 |
| 40 | .11382 | .10071 | .12195 | .10905 |
| 48 | .10195 | .09172 | .09478 | .08435 |
| 56 | .08439 | .07461 | .09006 | .08033 |
| 64 | .07162 | .06627 | .06662 | .06126 |

At depth64 both higher moments pass the `27/301` localization gate for both
profiles; depth48 left `s=3` narrowly misses. The data are nonmonotone across
profiles and finite depths. The oracle chooses input-dependent outputs and
assumes a tiny initial band; no fixed-provider or all-depth contraction
follows.

Reproduction: import `sparse_probe` and call `probe` with the parameters
above, `trace_stages=True`, and `initial='left'` or `'right'`. The exact
weighted-area identity was independently checked on 36,144 small
word/partition/moment cases for powers1..3. A fresh-context GPT-6-Luna review
confirmed the formulas and coefficient gate; it also emphasized that a
uniform all-profile fixed-provider transfer remains the decisive open step.

### Phase-dependent scalar weights: reduced-gate obstruction

The `STATUS.md` gate tested a common multiplier on three consecutive selected-cut transitions; it did not test a complete schedule period and therefore does not rule out a phase-periodic scalar multiplier. It does show that a common one-step coefficient of `1.1`, even with proportional local-defect charge, fails on those transitions in the reduced relaxation. Next screens should test the complete actual phase cycle, then move to a richer state if phase rescaling still fails. The gate remains a selected-cut relaxation, not a fixed-network impossibility result.

### Fourth-moment equality gate (2026-10-25)

I extended the exact small-flow diagnostic to `M_4` on the `(3,3,2)`
depth-4, scale-1 model, with all 4,097 global cuts and an ideal local refresh
at transition 1. The LP/MILP solves optimally with zero drift over transitions
0 to 2. Its returned solution is integral even without requiring integrality:
`M_4=1,000,541,859,856,575` at all three snapshots, while terminal wrong mass
is 1,447 (63 bad scalar terminal positions; maximum 64 in one block). The
model has 24,819 variables and zero equality/inequality residual.

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 4 --scale 1 --threshold 1/3 --ordered-prefix --root-tail --params 3 3 2 --row-bits 0 --time-limit 120 --all-global-cuts --exact-refresh-stage 1 --inversion-drift-stage 0 --inversion-drift-span 2 --inversion-prev-floor 1000000 --inversion-moment-order 4
```

This is a fourth-moment equality witness in the selected-cut profile model,
not a fixed-network trace. It joins the separate zero-drift `M_2` and `M_3`
gates and makes another unweighted distance power a poor next potential to
test. It does not show that one profile preserves all these moments
simultaneously; a better next gate is a profile-level adversary or a potential
that prices the actual D2 port transfer rather than only distance from the
threshold.

### All-row prefix-dominance profile equality (2026-10-25)

I strengthened the depth-4/scale-1 gate with prefix-dominance constraints at
every row (`--all-row-dominance --row-stride 1 --row-bits 3`) and saved its
all-cut profile to `LLM-helpers/sub300-m4-rowdom-profile.json`. The feasible
solution is fractional, so it is not a discrete trace, but its global
threshold-prefix defect `F(r)` is pointwise identical at all 4,097 cuts at
stages 0, 1, and 2: 3,414 cuts are nonzero and the maximum is 673. Thus every
global distance moment is also unchanged in this witness, even with all-row
local prefix dominance. This is evidence that marginal rank profiles alone
cannot certify contraction in this relaxation; it does not rule out a fixed
network, whose cross-cut correlations are absent from the model.

The useful next modeling step is to add a constraint coupling transfers across
neighboring cuts or ports, rather than adding more moments of `F`. The LP and
profile extraction are already fast enough for this small gate; moving the
arithmetic to C++ would not address the missing correlation information.

### Integral one-step profile-preservation gate (2026-10-25)

To check whether that conclusion was only a fractional artifact, I reran a
smaller depth-3, scale-1 model with `--integer`, all 513 global cuts, and
all-row local prefix dominance. HiGHS proves the maximum fourth-moment drift
over one transition is exactly zero (2,881 variables; 1,435 equalities and
7,930 inequalities). The saved integer-valued global profile is identical at
stages 0 and 1 at every cut (466 nonzero defects; maximum 86); the diagnostic
decomposes the same defect as entirely within-bag initially and entirely
cross-bag after that transition. The solver closes this MILP at the root node.

This removes fractional counts as an explanation for the one-step
noncontraction in this relaxation. It is still only an integral sequence of
profiles satisfying the current local dominance constraints, not a trace of
one fixed comparator network. These constraints omit the deterministic
cross-cut/port coupling imposed by the actual network. Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 3 --scale 1 --threshold 1/3 --ordered-prefix --root-tail --params 3 3 2 --row-bits 3 --all-row-dominance --row-stride 1 --all-global-cuts --time-limit 45 --integer --inversion-drift-stage 0 --inversion-drift-span 1 --inversion-prev-floor 1000000 --inversion-moment-order 4 --save-global-profile LLM-helpers/sub300-depth3-integer-profile.json
```
