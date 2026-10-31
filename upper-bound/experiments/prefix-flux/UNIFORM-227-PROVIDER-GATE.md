# Uniform-227 local-provider gate

This note isolates the first theorem-sized module for
[`UNIFORM-227-CANDIDATE.md`](UNIFORM-227-CANDIDATE.md). It is a parameter
audit, not a Lean proof or separator theorem.

## Per-role parameters

For every positive-fringe role, use
`delta=1/100000`, `J=30`, `c=1/2`, `b=5`,
`g1=floor(2f/5)`, and `g2=floor(4f/5)`. The exact role table and finite
minimum column counts are:

| Role | `f` | `g1` | `g2` | finite `n_min` | `delta*f*n_min` |
|---|---:|---:|---:|---:|---:|
| topRise | 32 | 12 | 25 | 4096 | 1.31072 |
| mid | 28 | 11 | 22 | 4096 | 1.14688 |
| botDesc, `r=1` | 28 | 11 | 22 | 8192 | 2.29376 |
| botDesc, `r=1/2` | 56 | 22 | 44 | 8192 | 4.58752 |
| botDesc, `r=1/4` | 56 | 22 | 44 | 2048 | 1.14688 |
| botDesc, `r=1/8` | 224 | 89 | 179 | 1024 | 2.29376 |
| botDesc, `r=1/16` | 448 | 179 | 358 | 1024 | 4.58752 |
| botDesc, `r=1/32` | 896 | 358 | 716 | 128 | 1.14688 |
| botDesc, `r=1/64` | 1792 | 716 | 1433 | 128 | 2.29376 |

`topDesc` has no fringe; `botRise` bypasses the provider. These minimum
columns are observed only through depth100. The weakest rank-cap slack is
`delta*f*n_min - 1 = 0.14688`, so an all-depth proof must preserve that
margin.

## Numerical envelope checked

`uniform_227_probability_screen.py` calls the interval-arithmetic certificate
in `walk-bound/fringe_cert_v2.py` with `exact_small=True` and a stricter
`failure_budget=1/10000`. The certificate computes SR, both R1 contributions,
and R2; its doubled `P1` (SR+R1) and `P2` (R2) envelopes each pass the
`1/10000` threshold for all seven `f` values. `exact_small=True` uses the
corrected exact `E=2` contribution instead of the generic tail expression.
The script also checks the rational monotonicity/Chernoff preconditions.

This is stronger than the earlier `1/1000` screen, but remains a numerical
interval certificate in Python. It is not an instance of `FringeCert` in
Lean: the generated Lean SR/R1/R2 certificates use unrelated large-fringe
parameters, and the exact `E=2` split has not been formalized here.

## Lean interface gap

The existing `F2Pre.hf16` requires `1 <= delta*f*16`; it fails for all these
parameters. It is used to establish `jmax(n)=floor(delta*f*n) >= 1` uniformly
for every `n>=16`. On this route each rectangle has `n>=n_min` and the table
gives `delta*f*n_min>1`, so a local premise `1 <= delta*f*n` should suffice
for that floor argument. However, SR and R1 failure lemmas also take the
global `F2Pre` and `n>=16`; they need a checked local-`n` variant, not just a
rewritten `jE_factsd` lemma.

For the tight `f=28` SR instance, a plausible integer certificate starts with
`T=f-g1+1=18`, `K0=ceil(J/(g1+1))=3`, and `Xn=5`; one still must choose and
verify `qd,N` against `SRd_numeric`'s natural-number inequality. R1 needs the
existing `R1aNumd` and `R1bNumd` inequalities proved for every role. R2 needs
the exact `E=2` contribution exposed as a Lean lemma and the remaining closed
tail certified. Finally, the wrapper needs simultaneous SR/R1/R2 witnesses
for each role, both orientations, and the separator's baseline conditions.

## Decisive bulk-provider obstruction

The local separator contract also needs two-sided `HasPackSemanticPropertyB2`;
the F2 screen above does not provide it. The checked route in
`TwoRoundSeparatorExists` hard-codes `m >= 2^42` for B2, and its ordinary-node
wrapper additionally hard-codes a 64-child shape. The U rectangles have
`m <= 8192` and eight equal children, so that theorem cannot instantiate.

The size threshold is not merely a wrapper artifact for the existing B2
proof. In `failBoundB2`, its round-two exponent is

```text
m * K,  K = lambda*d/2 - lambda^2*(1/2 + 2*lambda/9)*E1,
```

while the state-and-subset union contributes approximately
`n*log(2*(m+1))`. With `d=1/59000000` and `E1=371/10^8`, maximizing K over
`0 < lambda <= 1` at `m=8192` gives `K ~= 9.67e-12`, hence `m*K ~= 7.93e-8`
versus `log(2*(m+1)) ~= 9.70`. The current union-bound argument misses by
about eight orders of magnitude in the exponent per column. This diagnoses
this proof method and constants; it is not an impossibility theorem for small
row B2.

The same calculation quantifies how much relaxing the B2 target would cost.
For `n=16`, making this union bound at most `1/1000` requires
`m*K >= log(2*(m+1)) + log(1000)/16`. At `m=8192`, keeping the current
`E1=371/10^8` and taking the optimizing endpoint `lambda=1` requires roughly
`d=0.00248`, about 146,000 times the present `d=1/59000000`. Since the semantic
B2 leakage allowance is `d/2` of `mn`, this is about `0.124%` of the rectangle.
That relaxed constant is only a diagnostic target for the existing union
bound; the global rank/prefix recurrence would have to show that such errors
still contract to exact terminal purity.

The strategic escape is to avoid universal B2 over every monotone column
profile: prove a stronger reachability invariant for uniform U, then establish
the bulk estimate only on profiles that can arrive at each node. Existing
UB-42 profile experiments are for D2 and do not transfer automatically; a
U-specific recurrence and terminal-purity gate are required. Alternatively,
a new small-row bulk provider must improve the exponent/state-count balance
without spending enough extra row-sort layers to lose the target coefficient.

## All-depth geometry reduction

The finite role scan admits a short exact reduction. For `t>=2`, write
`q(d,t)=ceil((2t-3d+10)/2)`. The schedule's `alpha(d,t)` is the least
nonnegative integer congruent to `t mod 2` that is at least `q(d,t)`, and
`omega(t)` is the least integer congruent to `t mod 2` at least
`ceil((2t+3)/5)`. Thus `omega(t+10)=omega(t)+4`.

For a processed bottom sender `i=omega(t)`, the stage condition is
`alpha(d,t)<omega(t)` (the terminal `t=tf(d)` stage is not processed; the
source `active()` predicate alone permits that endpoint), and
the level constraint is `d>=omega(t)`. Since `omega(t)>=2`, the alpha
inequality is equivalent to

```text
3d >= 2t - 2*omega(t) + 14.
```

Consequently the least admissible depth is
`d0(t)=max(3,omega(t),ceil((2t-2*omega(t)+14)/3))`. For `t>=2`,
`d0(t+10)=d0(t)+4`; at every fixed `t`, increasing `d` beyond `d0(t)`
increases the cap exponent `C=3d+2*omega(t)-2t-3` by3 and hence multiplies
all column counts by8. The exponent `e=2t-5*omega(t)+3` of
`native/c=2^e` and the endpoint role are periodic under `t -> t+10`.
Therefore all bottom role minima reduce to ten exact cases:

| `t` representative | `omega` | `d0` | `C` | `e` | role / `n_min` |
|---:|---:|---:|---:|---:|---|
| 2 | 2 | 5 | 12 | -3 | botDesc `r=1/8`, 1024 |
| 3 | 3 | 5 | 12 | -6 | botDesc `r=1/64`, 128 |
| 4 | 4 | 5 | 12 | -9 | botRise bypass |
| 5 | 3 | 6 | 11 | -2 | botDesc `r=1/4`, 2048 |
| 6 | 4 | 6 | 11 | -5 | botDesc `r=1/32`, 128 |
| 7 | 5 | 6 | 11 | -8 | botRise bypass |
| 8 | 4 | 8 | 13 | -1 | botDesc `r=1/2`, 8192 |
| 9 | 5 | 8 | 13 | -4 | botDesc `r=1/16`, 1024 |
| 10 | 6 | 8 | 13 | -7 | botRise bypass |
| 11 | 5 | 9 | 12 | 0 | botDesc `r=1`, 8192 |

The omitted representative `t=1` is an alpha-boundary node and uses the
top-role rule, not a bottom provider. For interior nodes, `i>=alpha+2`, so
`C=3d+2i-2t-3>=11`; this proves `n=2c>=4096` for every mid role. A topDesc
with `t>=2` has `i=alpha`, giving `C>=7`; the special `t=1` case has
`C=3d-3>=6` for `d>=3`. In both cases `n=2048c` is integral and large. A topRise
for `t>=2` can only be the parity drop `alpha=1 -> 0`, which forces
`3d>=2t+12` and hence `C>=11`; the special `t=1` topRise requires `d>=5`
and has `C>=12`. Thus topRise also has `n>=4096`. The root is handled
separately. These inequalities and the ten-case bottom table appear to close
all-depth rectangle divisibility, `n>=16`, and positive-rank-cap conditions
for the proposed role table. They remain a paper derivation pending fresh
review; the current scripts only check finite depths.

The other schedule asymptotics follow from the same rounded formulas:
`alpha(d,t)=t-3d/2+O(1)`, `omega(t)=2t/5+O(1)`, so the first crossing
`tf(d)` satisfies `tf(d)=5d/2+O(1)` and
`d-omega(tf(d))=O(1)`. The latter gives constant-size terminal native
subtrees, but the exact crossing constants and scheduler endpoint convention
still need a proof.

## Smallest next gate

1. Resolve the B2 bulk gate above: either give a small-row two-sided provider
   with explicit constants, or replace universal B2 by a U-reachable-profile
   invariant whose bulk error composes to terminal purity. The present
   `1/59000000` union bound is quantitatively unusable at `m<=8192`.

2. Prove all-depth lower bounds for the role-wise `n_min` (or directly prove
   `delta*f*n>=1` and `16<=n` for every active positive-fringe sender).
3. Audit every use of `F2Pre.hf16`; formulate local-`n` SR/R1/R2 variants
   without broadening unrelated theorem assumptions.
4. Formalize and certify the corrected `E=2` R2 term at `f=28` and the
   smallest-column `f=56`/`896` cases before generating seven parameter files.
5. Establish the shared-witness union with the actual baseline, both
   orientations, and the global scheduler's finite set of role classes.

Do not start the Lean provider until these five obligations and the global
rank/prefix transfer are reviewed together. The conditional coefficient
227.5 is not yet a proved sorting bound.
