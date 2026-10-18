# Tournament pair witnesses and the universal-proof gap

Derived argument, 2026-10-10; informal and not Lean checked. This sharpens the
fixed-input estimate for [the 86-layer funnels](fresh-reservoir-funnels.md).
It does not establish a common network witness for all inputs.

## Why the first estimate lost too much

The original calculation replaced every later exterior pair count by the
initial pair count. A first tournament already removes almost all pairs. It
is enough to estimate its second factorial moment, then use monotonicity of
the exterior count for all later phases. No independence between phases'
exterior states is assumed.

Fix a column and its initial exterior set of `H` high marks. Write `s` for the
largest group size in the first balanced partition and set

```
kappa = (s-1)/(M-1),
tau   = (s-1)*(s-2)/((M-1)*(M-2)),
q     = (s-1)^2/((M-2)*(M-3)).
```

Fresh roots are in distinct rows. Their high indicators are independent in
this fixed column, independent of its exterior state and partition, and each
has probability at most `p`. This does not assert independence across columns.

Track abstract labels on exterior high marks. A group with a low root loses
one label if nonempty; a group with a high root retains all its labels. This
matches the binary count even if the physical high keys exchange identities.
For two specified distinct labels to survive:

- In the same group, its root must be high, or a third exterior mark must be
  present. These events have probabilities at most `p*kappa` and
  `(H-2)*tau`, respectively.
- In different groups, either both roots are high; or one root is high and
  the other group has another exterior mark; or each group has another mark.
  The corresponding bounds are `p^2`, `2*p*(H-2)*kappa`, and
  `(H-2)*(H-3)*q`.

The two partner marks in the last case must be distinct. Sampling a balanced
partition is sampling group slots without replacement. Three specified marks
share a group with probability at most `tau`. Two specified disjoint pairs
each share a group with probability at most `q`; after exposing one pair,
the probability that the remaining partner matches is at most
`(s-1)/(M-3)`, and the displayed `q` is a conservative bound.

Summing over ordered pairs, with `(H)_k` the falling factorial, proves

```
E[(H_1)_2 | H_0=H]
 <= (p^2+p*kappa)*(H)_2
  + (2*p*kappa+tau)*(H)_3
  + q*(H)_4.
```

This is an upper bound: the presence of a third mark need not actually keep
both selected labels. That overcount is harmless.

## Initial moments and numerical consequence

Initially, in each column the exterior marks come from independent row
scrambles. They are independent Bernoulli variables across rows. Their common
column mean `mu_j` is at most `eta*j/n`. Expanding the falling factorial gives
`E[(H_0)_k]<=mu_j^k`. Put `mu=eta*a0` and define

```
C = p^2+p*kappa + (2*p*kappa+tau)*mu + q*mu^2.
```

Because `j/n<=a0`, summing over columns yields

```
sum_columns E[(H_1)_2] <= C*eta^2*j^2/n.
```

The exterior count decreases pointwise, so this same bound applies to the
second factorial moment before phases 2, 3, and 4. Iterating the original
first-moment recurrence now gives the expected total fringe escape bound
`B_new*j`, where

```
B_new = 40/T + eta*p^4
      + eta^2*a0/2 * [p^3*kappa_0
                    + C*(p^2*kappa_1+p*kappa_2+kappa_3)].
```

With the original four reservoir sizes and `eta=1/3650`, exact rational
arithmetic gives

```
C = approximately 0.002733311100167142
B_new = approximately 6.269879586161310e-9
B_new/epsilon = approximately 0.5392096444098727.
```

Thus the error margin is about **46%**, rather than 0.55%, without adding any
layers. The untouched mass beyond the window contributes `40/T`, about
`4.6566e-9`; the tournament contribution is about `1.6133e-9`.

## What a bad tournament witness looks like

### Stronger blocking bounds from the same tail promise

Choose the four chunks consecutively upwards from `g`, in the listed order.
Their first row offsets above `g` are `1,473,2361,10857`. For a root at offset
`u`, each source column high at that row contributes at least `u` to `E_g`.
Thus its high probability is at most `eta*j/(n*u)`, as well as `p`.
We can consequently use the phase-specific bounds

```
p_i = min(p, eta*a0/u_i)
    = approximately [0.04885496, 0.00237250, 0.00047530, 0.00010336].
```

The first-phase pair constant `C` is unchanged. Re-evaluate the first-moment
recurrence with these four different bounds:

```
b_0 = eta
b_(i+1) = p_i*b_i + eta^2*a0*kappa_i*c_i/2
c_0=1; c_1=c_2=c_3=C
B_strong = 40/T + b_4
         = approximately 4.668180720323884e-9
B_strong/epsilon = approximately 0.4014635419478541.
```

These are exact-rational evaluations of the displayed bounds. The expected
error is now about **40%** of the target, at the same depth. Almost all of this
ceiling is the untouched-window allowance `40/T`; the tournament contribution
is below `1.16e-11*j`. This stronger root estimate is also relevant to a joint
witness calculation: four blocking-root events have very different costs,
and treating every root as having density `a0/g` loses substantial information.

### Dependency graph instead of independent trees

For one labelled survivor, at each phase its group either had a high root or
had another exterior high mark. Recursively tracing a required partner back
through previous phases produces a depth-four dependency tree. A single tree
has at most 16 initial exterior leaves and 15 root certificates. These are
necessary-event certificates, not independent trials.

For many final survivors the trees can share partners, roots, or groups. An
output group with `k` survivors needs `k` initial exterior marks and either a
high root or one additional mark. In particular, charging one fresh binary
tree to each survivor overcounts independent evidence. A correct joint
witness must merge such shared groups into a dependency graph and retain its
actual number of distinct row-slot marks and partition coincidences.

The source profile also matters: a selected high slot in row `t` forces its
source column's sorted height to be at least `t`. Multiple slots can be
supplied by one tall source column. Counting slots as separate source columns
would give a false entropy bound.

## Next proof obligation

For each supported rank `j`, count reduced dependency graphs together with
their reduced monotone source profiles, and bound their joint probability
under row permutations and balanced partitions. Then sum over ranks and both
orientations, using the *same* first scramble, second scramble, and partitions.

The acceptance condition is that this sum is below the probability mass left
after enforcing the other separator promises. A fixed-input exponential tail
alone does not suffice unless it beats the number of admissible profiles.
Nor does the better expectation automatically supply such a tail. Its Markov
bound is still about 0.539 per fixed input, which cannot cover the whole class.

The calculations remove the previous narrow expectation margin as the main
concern. The unresolved issue is now the entropy of shared dependency graphs
and their sorted source profiles. Before formalizing a universal claim, derive
a scalar entropy-versus-probability inequality and check that it is negative
throughout the supported parameter range. Bulk repair and scheduler adapters
remain separate obligations.

Only research arithmetic was evaluated. No tests, Lean builds, or production
proof changes were made.
