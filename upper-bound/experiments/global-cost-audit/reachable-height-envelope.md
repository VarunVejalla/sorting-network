# Reachable heights and the smaller-fringe decision

Informal mathematical investigation, 2026-10-10. No new Lean theorem,
comparator network, or global upper bound is claimed.

## Main findings

1. The present coupled first/second fringe bounds do not close at `f=131040`.
2. The first scramble can satisfy a useful additional universal height bound:
   at every supported large rank `j>=86000000`, every intermediate sorted
   column has fewer than `ceil(16*sqrt(j))` marked keys, in both orientations.
3. This bound excludes the earlier single-long-column witness, but a many-column
   witness at larger ranks restores the 26-layer obstruction on the enlarged
   state class. The additional height promise alone is insufficient.

## A simultaneous height-envelope argument

Take `a0=8192`, `J=86000000`, `m>=1`, and `n>=16`. Consider all sorted Boolean
input profiles of mass `J<=j<=floor(a0*n)`. Use independent uniform row
scrambles. Fix an output column and suppose it receives at least
`ceil(16*sqrt(j))` marks. Retain that many hits and reduce each source column
to its last retained row height, measured from the bottom.

The reduced input mass is at most `j`. If there are `d` active sources, their
last heights are distinct, giving `d*(d+1)/2<=j`. Thus

```
d <= sqrt(2*j) <= D = (3/2)*sqrt(j).
```

There are at most `binom(n,d)*binom(j,d)` possible reduced profiles. For each
fixed valid profile, the fixed-column tail bound gives

```
P[at least 16*sqrt(j) hits] <= (e*j/(16*n*sqrt(j)))^(16*sqrt(j)).
```

The real threshold is allowed by the existing tail theorem; an integer bad
count exceeding it satisfies that event. If the threshold exceeds `m`, the
event is impossible.

Put `u=sqrt(j)` and `v=n*a0/j>=1`. The profile entropy function is increasing
up to `D`, since `n*j/D^2=n/(9/4)>1`. Union over profiles and output columns
therefore gives, for one orientation at fixed `j`,

```
P_j <= (3*u^3/(2*a0))
       * exp(u*[ (3/2)*ln(4*u^2/a0)
                 +16*ln(3*a0/(16*u)) ])
       * v^(1+D-16*u).
```

Here `e<3` bounds the bases, and `1+D-16*u<0`, so the last factor is at most
one. The exponent bracket is

```
(3/2)*ln(4/a0)+16*ln(3*a0/16)-13*ln(u).
```

It decreases with `u`. At `u=sqrt(J)`, exact rational logarithm intervals
give an upper bound below `-12` (approximate display: `-12.8000139`). Hence

```
P_j <= (3/(2*a0))*j^(3/2)*exp(-12*sqrt(j)).
```

To cover all ranks, group integers by `ell=floor(sqrt(j))>=9273`. Each group
has at most `2*ell+1` ranks, and `j^(3/2)<=(ell+1)^3`. For both orientations,

```
P_any <= (9/a0)*sum_{ell>=9273} (ell+1)^4*exp(-12*ell)
      <= (18/a0)*9274^4*exp(-111276)
      < 10^(-33000).
```

The consecutive-term ratio is at most `16*exp(-12)<1/2`, justifying the
geometric bound. The last comparison follows already from `e>2` and
`2^10>10^3`, with a prefactor below `10^14`.

This covers all supported ranks and all input profiles for one scramble,
uniformly in unbounded `n`. The source-profile reductions still need formal
adapters, but the argument has the same finite common-witness quantifiers as
the earlier small-rank proof. Its bad event can be union bounded with bulk
mixing and the moderate inner-fringe theorem to choose one first scramble.

For `a0<=8192` the same envelope proof is valid: use the stronger supported
mass promise `j<=8192*n` when bounding its probability. The moderate
inner-fringe parameters themselves must still be checked separately.

## Why the enlarged-class obstruction no longer applies

The [previous obstruction](repair-cone-obstruction.md) allowed an intermediate
column of height `m` at mass roughly `j=(m-g)/eta`, with `eta=1/5800`.
For the large template heights,

```
16*sqrt((m-g)/eta) << m.
```

Thus that profile violates the new reachable-height promise. It cannot be
used to prove the same depth lower bound for a first scramble selected to
obey this additional theorem.

As a diagnostic, the maximum over real `j>=0` of

```
16*sqrt(j)-epsilon*j
```

is `64/epsilon=5504000000`. At `f=262080`, `f*2^15` exceeds this number. So
the corresponding single-column ancestor coverage requirement does not force
26 layers once this envelope is included. This is only a necessary-condition
calculation. It is not evidence that 15 layers suffice: many columns, all
rank thresholds, physical routing, and bulk cuts must still be handled.

## A many-column witness restores the barrier

The maximum-height envelope becomes vacuous at sufficiently large ranks.
This matters because the support `j<=a0*n` allows arbitrarily large `j` as
`n` grows, even at fixed matrix height.

For an exact instance choose

```
m=2^43, f=262080, g=157248,
j=m^2, n=m^2/8192, a=floor(m/11600).
```

Mark `a` source columns completely. Fill the remaining mass `j-a*m` in other
columns of height at most `g`. This is possible because
`g*(n-a)>=j-a*m`. These profiles meet both strengthened promises:

```
E_g=a*(m-g)<j/5800,
maximum height=m<16*sqrt(j).
```

They also have exactly the supported mass `j=8192*n`. The other heights can
be chosen as evenly as possible near 8192; the aggregate absolute deviation
of heights from their mean remains small (approximately 1.42), rather than
violating the first bulk estimate at this threshold. This does not prove that
the profiles are reachable after the selected first scramble.

Average over the choice of the `a` tall source columns after the fixed second
scramble. For any column-local depth-`d` repair, the expected number of tall
marked keys outside their destination fringes' ancestor sets is at least

```
a*(m-f*2^d).
```

Hence some source-set choice leaves that many keys outside the fringe,
regardless of how the background mass is filled. At depth 25 the uncovered
fraction is `1/4096`, and

```
a*m/4096 > j/86000000.
```

The last inequality, together with the support and padding inequalities,
was checked with exact integer arithmetic at the displayed instance.
Thus a repair required to handle this enlarged class still needs at least
26 layers. The 19-layer budget is still impossible on that interface.

This is not a counterexample to the actual first-scramble reachable family.
It proves that **maximum height plus one inner-fringe tail-mass bound** does
not describe that family strongly enough to escape the existing barrier.

## Smaller fringe: what was actually checked

For `f=131040`, let `g` vary, `H=g/2`, `h=f-g`, and `a0=4096`. The two
analytic scalar conditions from the relative-fringe note are

```
C1 = [1+ln(H/(eta*a0))]/H
     +[2+ln(H^2/a0)]/(eta*H)+1+ln(a0/H) < 0,

r = sqrt(eta*J/(2*h)),
C2 = [1+ln(J*h/a0)]/h
     +r*[2+ln(J*h/(2*a0))]+1+ln(eta*a0/h) < 0.
```

A floating-point scan of `g/f` and `eta`, including bisection near the
`C1=0` boundary, found no feasible pair. Evaluating the less-relaxed second
exponent also remained positive: near `g/f=.64`, `eta=.00026930`, its largest
sampled normalized exponent was about `+.5534` at `j/s` around `4.1e12`.

This is a failure of the present sufficient estimates, not an impossibility
theorem, global optimizer certificate, or lower bound on the actual failure
probability. The new maximum-height bound does not immediately fix this
entropy count: the adverse counted profiles use many moderate-height tails,
not necessarily one height-`m` column. A sharper reachable-profile count would
need more than this envelope.

## The useful next construction target

The updated repair input interface can now include all of:

- first-stage bulk control;
- moderate inner-fringe tail mass `E_g<eta*j`;
- maximum intermediate height `<ceil(16*sqrt(j))` for `j>=J`;
- exact fringe-row confinement at small ranks;
- the fixed second row scramble and its joint ideal bulk/fringe guarantees.

Attempt a physical threshold repair on this class, without assuming it is
nearly sorted or that its capture window may depend on the unknown rank of
an individual key. The envelope supplies rank-dependent containment; one
fixed comparator network must still work for all ranks simultaneously.

For below 1000 there remain two separate budget options:

1. close the relative-fringe theorem at smaller scale, leaving up to 107
   repair layers; or
2. at the larger scale, prove an aggregate reachability restriction stronger
   than the current height-plus-tail promise, then construct a repair within
   the 19 layers left by two complete bitonic sorts.

Neither construction is currently supplied. The second is particularly tight,
and the many-column witness defeats the currently proposed strengthened
interface. A complete candidate must also handle all 65 bulk cuts and the
small-node fallback. The conditional full-sort route near coefficient 1485
remains distinct from these sub-1000 targets.

A more informative next lemma would constrain the whole height distribution,
for example the numbers of columns above each row height or the profile tails
`E_t=sum_c(max(z_c-t,0))` for multiple `t`, with one common first witness.
It must exclude the many-tall-column profile at supported large ranks and
come with an explicit repair argument. Another isolated maximum-height bound
will not accomplish this. Alternatively, prioritize the smaller-scale fringe
proof, where the 107-layer repair budget survives the 26-layer obstruction.

## Verification scope

Source review and mathematical derivation only. The coefficient `<-12` was
checked using exact rational logarithm intervals in
`../paterson/uniform_concentration.py`; the parameter scan was exploratory
floating-point arithmetic. No Lean files, tests, or builds were run.
