# Two-round fringe: exact small-rank reduction

Research analysis, 2026-10-10. No Lean files were created or modified. Arguments
are derived and unaudited, not kernel-checked. Scratch work remains in the
gitignored `LLM-helpers/`; future scratch Lean must likewise stay outside
`chvatal-1830` until promotion.

Let J=86000000 (a constant, not a multiple of the matrix height),
epsilon=1/J, and delta=128/4095. At supported ranks `j <= J`, the strict
contract `escaped < epsilon*j` requires zero escaped keys.

## 1. Deterministic small-rank propagation lemma

Let z be the sorted column heights after the first scramble. Define
`E_g(z)=sum_c (z_c-g)_+`. If

`E_g(z) < eta*j` and `g+eta*j <= f`,

then every z_c is at most f: each individual excess is at most E_g(z).
Thus all marked cells lie in the bottom f rows. A row scramble preserves these
rows, and a column sort keeps every mark there. The entire second round has
zero escaped marks, regardless of its permutations.

For all `j <= J`, it suffices that `eta <= (f-g)/J`. This is a conditional
all-input lemma, not an existence theorem for the first scramble. It also shows
that in this regime the second round is not needed to eliminate escapes once
the premise holds.

The first-round existence contract must cover the full relevant rank interval
`j <= min(J,delta*f*n)`. A sufficient support condition for a theorem formulated
as `j <= deltaPrime*g*n` is `deltaPrime*g >= delta*f`. In particular g=f/2
requires doubling the supported relative rank range. This change cannot be
silently inferred from the existing theorem.

## 2. Candidate weaker first-round parameters

The needed intermediate accuracy is much weaker than epsilon. For example,
f=131040, g=65520 allows eta<=0.0007618605, but doubles the support fraction.

The existing entropy expression can be explored with epsilon replaced by eta,
fringe f replaced by g, and maximal rank ratio `v=delta*f/g`. This does not
generalize the existing Lean theorem automatically: its numeric and rounding
hypotheses must be re-proved.

Exploratory values of that expression at eta=(f-g)/J are:

| Final f | Intermediate g | eta | xval at maximal supported ratio |
| --- | ---: | ---: | ---: |
| 131040 | 91728 | 0.00045712 | 0.5002 |
| 200000 | 150000 | 0.00058140 | 0.3249 |
| 262080 | 209664 | 0.00060949 | 0.2734 |

The original xval target 0.32 suggests a credible small-rank sufficient regime
around the third row, if the generalized proof and rank rounding survive.
These numbers are floating-point probes, not certificates. There are separate
tail-ratio, rounding, two-sided, and common-witness probability obligations.
This candidate only addresses j<=J, not the full fringe contract.

A more concrete rational candidate in the third regime is
`g=209664`, `f=262080`, `eta=1/1641`. Then eta*J is approximately 52407.07,
below f-g=52416. Rounding ranks to multiples of 1641 increases the supported
ratio by at most `1641/(16*g)`; the rounded ratio remains below 0.04. At the
cap v=0.04, the generalized xval is approximately 0.2798 (floating point).
This removes the old 86000000-sized rounding jump for the weaker intermediate
contract, but all generalized tail and counting statements still need proof.

## 3. Two-round adversary with a tighter mass bound

Fix both row scrambles and one target output column. Select its last-scramble
preimages in the bottom k rows. For each intermediate column c, let q_c be
the largest selected row height there. To ensure those marks after the first
sort, demand its bottom q_c cells, pull them back through the first scramble,
and downward-close in the input columns.

The resulting input mass satisfies

`j <= sum_c q_c*(q_c+1)/2
   <= sum_{r=1}^k r*(r+1)/2
   = k*(k+1)*(k+2)/6`.

The middle inequality assigns each maximum q_c to a distinct selected row;
all summands are nonnegative. The final target has at least k marks, hence
at least k-f escapes. At sufficiently large n the input rank is supported.

Taking k=2f yields the necessary strict condition

`epsilon*(2f+1)*(2f+2) > 3`.

At today's epsilon this requires f>=8031. This bound is not optimized over k;
it is enough to show the much weaker two-round obstruction compared with
the one-round requirement f>=43000000.

Taking k=f+1 gives one escape at input mass at most
`(f+1)*(f+2)*(f+3)/6`. At f=131040 this is about 3.75e14, far above J.
It therefore does not refute zero escapes throughout the small-rank interval.

Collision-rich intermediate preimages can reduce this mass, but arbitrarily
large n alone does not force them: row translations with distinct offsets
can give distinct preimages for each single target's selected rows. Such
translations are not a positive separator construction; they merely invalidate
that particular pigeonhole obstruction.

## 4. Remaining probability problem

For general j>J, small-rank propagation no longer supplies the epsilon-relative
bound. A joint witness must preserve simultaneous intermediate demands, rather
than closing each demanded cell independently and treating their overlaps as
independent. The exact target condition is:

For each rank j and output subset S, bound the probability that some sorted
input of mass j produces excess at least epsilon*j in S after both rounds;
then sum over ranks and subsets uniformly in n.

No such uniform tail/counting inequality has been established here. Neither
the favorable two-round obstruction nor the small-rank propagation lemma
implies it.

## Next modular milestone

Generalize the existing one-round F existence argument to eta, g, and the
required expanded support fraction, only for the small-rank interval. This
is a concrete tractable branch with explicit hypotheses. In parallel with
that mathematical work, the high-rank joint-witness inequality remains the
main new research obligation. Keep both separate from bulk accuracy and the
global depth budget.
