# Joint profile-weighted MGF screen

2026-10-21. UB-42 research diagnostic; no improved sorting bound.

## Idea

The existing moderate-tail estimate bounds the number of possible column
profiles and then uses the worst row-scramble MGF for every profile. These two
worst cases need not occur at the same profile. Keep the profile sum inside
the Chernoff bound instead.

For an `m`-by-`n` rectangle, let `c_j` be the initial height in column `j`,
and `u_r = #{j : c_j > r}` the number of marked positions in row `r`. For a
fixed output subset `S` of `s` columns, independent uniform row permutations
give independent hypergeometric variables

    X_r ~ Hypergeom(n, u_r, s),   X_S = sum_r X_r.

For a mass cap `H`, sum the moment weights over all labeled profiles:

    Z(theta) = sum_{c in {0,...,m}^n, sum c_j <= H}
                 product_{r=0}^{m-1} E[exp(theta X_r)].

Thus a union bound for an escape threshold `x + f*s`, over every subset size
and subset, is

    P(any escape) <= sum_{s=1}^n C(n,s) exp(-theta*(x+f*s)) Z_s(theta).

`profile_mgf_dp.py` computes `Z_s` exactly as a finite sum (with floating
arithmetic): row populations form a nonincreasing chain, and the transition
from `u` to `v <= u` has multiplicity `C(u,v)`. This counts each labeled
height vector once. The finite check at `(m,n,H,s,theta)=(6,8,16,4,1)` agrees
with independent direct profile enumeration to displayed precision; the
absolute difference of the exponentiated sums is `2.4e-6` from float
accumulation. For the same parameters and `eta=10^-3`, the screen gives escape
allowances `10,7` for fringe widths `2,3`; the matched analytic envelope gives
`13.31,12.09`. This is a small finite experiment, not a uniform estimate.

## Fixed-height asymptotic rate

For fixed `m` and `n -> infinity`, a profile type `nu` on `{0,...,m}` has
row fractions `a_r = sum_{j>r} nu_j` and entropy `H(nu)`. The profile-type
sum has exponential rate

    R_m(i,p,theta) = max_{nu: E_nu[j] <= i}
       ( H(nu) + sum_{r=0}^{m-1} psi(a_r,p,theta) ),

where `p=s/n` and `psi` is the limiting log-MGF per column of
`Hypergeom(n, a*n, p*n)`. The number of types is polynomial in `n` for fixed
`m`, so it contributes zero to the limiting rate. The objective is concave:
entropy is concave and `psi` is concave in `a` (from the entropy-perspective
representation of the hypergeometric rate). A tangent plane at a strictly
positive feasible profile, evaluated with the exact gradient, therefore
gives a global upper bound, optimized over the simplex and mean constraint
by a small linear program.

The script's `asymptotic_profile_fixedpoint` uses floating-point KKT
iterations and a floating LP tangent-plane calculation. A fresh GPT-6-Luna
review found a flaw in the original tangent path: exponentials underflowed to
zero, the entropy gradient clipped zero coordinates to a finite slope (not a
supergradient), and endpoint derivative approximations were inaccurate near
`a=1`. The final tangent evaluation has since been revised to mix in a
positive polynomial tail and use a bracketed saddle solve for derivatives.
Follow-up review confirmed that this fixes the zero-coordinate entropy slope
and final derivative endpoint issues. It also found the value still uses a
first-order small-`a` rate approximation, so the evaluated value and gradient
are not exactly the same objective; the floating LP/rate evaluation also has
no interval enclosure. The tangent gaps are therefore not certified upper
bounds. All asymptotic allowance values below remain exploratory estimates;
they do not establish that the true profile rate is below the separated
bound. The exact finite Chernoff screen and asymptotic variational calculation
are separate:
the former is finite but only practically computable for small `n`, while the
latter is the relevant fixed-`m`, large-`n` candidate but still needs certified
optimization and uniform parameter control.

## Current numerical signal and decision

At `m=4096`, a coarse `p in {0.1,0.25,0.35,0.5,0.65,0.8,0.9}` and
`theta in {0.5,1,2,4,6,8}` sweep, with `f=2`, found the following minimum
weighted escape rates versus the separated envelope:

| mass class `i` | sampled `p` | joint-profile optimizer estimate | separated allowance |
|---:|---:|---:|---:|
| 2 | 0.35 | 1.2434 | 1.3778 |
| 11 | 0.80 | 9.4727 | 9.5861 |

The grid's largest optimizer-estimated allowance for `i=2` was `1.2434`; for
`i=11` it was `9.4727`. These are grid observations, not certified suprema
over `p`, and the fixed-point tangent calculations are invalid as upper
certificates for the reasons above. They suggest a possible modest local-tail
gain, especially at sparse mass, but do not prove one. A subsequent exact
finite profile-conditioned probability screen is sharper than the finite MGF
screen at the tested sizes, so the finite MGF values should not be treated as
the best numerical evidence either. Neither method addresses the decisive
UB-42 gap: a coupled rank-profile transfer through the actual D2
ports that forces all terminal noncrossing blocks to be pure. The prior
ordered LP relaxation leaves `456,448` wrong terminal keys at depth 6 / scale
4096 even with sampled local dominance cuts. No coefficient improvement or
Lean formalization follows from this MGF screen alone.

The next meaningful gate is to repair the interior tangent computation with
strictly positive feasible profiles and correct endpoint derivatives, then
certify the asymptotic rate envelope (including
uniform `p`, `theta`, mass class, and finite-size terms) and substitute it in
the same coupled global recurrence. If that recurrence still leaves remote
terminal defects, this tail refinement is not enough for the 292.5-cost
candidate.
