# Chvatal separator requirements and multi-round costs

Source review: 2026-10-10, current `chvatal-1830` sources. This is a research
analysis, not a new kernel-checked bound. No Lean sources were changed.

Follow-up: [two-round separator analysis](chvatal-two-round-separator.md) derives
a stronger simultaneous bulk argument and identifies the scheduler's very small
fringe ratio as an additional obstruction. Its cost analysis supersedes the
optimistic full-sort estimates below.

## Contract consumed by the scheduler

`AKS/Chvatal/NodeSpec.lean` exposes four guarantees for every input permutation:

| Guarantee | Required behavior | Consumer |
| --- | --- | --- |
| `bLow`, `bHigh` | At each of 65 block boundaries, misplaced extreme ranks are at most `EB` | `BadSendReal`, `BadSendField` |
| `fLow`, `fHigh` | For every `0 < j <= Jmax`, fewer than `epsF*j` of the smallest/largest `j` keys miss the appropriate fringe | `FringeSendReal`, `FringeSendField` |

Ordinary nodes currently use `EB = paperOrdinaryEpsB*a/2`, with
`paperOrdinaryEpsB <= 1/59000000`, `epsF = 1/86000000`, and
`Jmax = floor((128/4095)*(up/2))`. Thus the bulk allowance is at most
`a/118000000`. The extreme-rank guarantee is relative, not an additive bulk
allowance. In particular, every supported `j <= 86000000` must have zero misses.

The fringe bounds feed a hierarchy of stranger counts; they are not merely a
second version of the bulk bound. Proving a small average bulk error does not
establish the current interface. The implementation sorts entire columns, but
the global scheduler consumes these four rank guarantees, not column sortedness.
Column sortedness is essential to the present local scramble proofs.

## Where the coefficient comes from

`DepthSkeleton` has `3*d-21` ordinary rounds for `64^d` inputs, i.e. asymptotically
one round per two binary logarithms. `RealNets.nodeGood_geom` budgets each
ordinary pack by two bitonic column sorts with `m <= 2^59`:

`C = ordinaryDepth/2 = [2*(59*60/2)]/2 = 1770`.

Root depth 6320 and final cleanup 903 are additive constants. Reducing these
alone cannot improve the limsup coefficient. Keeping the scheduler requires
ordinary depth at most 400 to reach coefficient 200.

The bulk concentration theorem requires
`epsB >= sqrt(2*(1+ln m)/m)`, hence column sizes around `2^58` for today's
bulk error. Independently, the present fringe existence proof requires
`f >= 8500000000` when a fringe is present, with `m = 2*f+64*b`.
Consequently, even removing the bulk restriction would not allow tiny columns
without replacing the fringe argument. These are sufficient conditions of the
current proof, not lower bounds on all separator constructions.

## Review of the multi-round simulation

Reviewed `.claude/worktrees/multiround-sim/scripts/multiround_sim.py`.
Part A follows threshold column sums under fresh random row permutations;
Part B measures within-column displacement for selected distinct-key families.
The main CLI uses exact row permutations. An additional independent-column
sampler preserves one-step column marginals but not joint dependence or the
exact conserved sum. The floating-point mean-field routines describe a limiting
model, not a finite-size certificate.

The measured bulk statistic is `L1/(m*n)` at the mean threshold. The current
Property B contract also covers cutoffs away from the mean; relating their
excess counts to this statistic is necessary. Neither simulation part tests
the relative extreme-rank contract. The script's claim about ANY fixed scramble
via random inputs is not justified by its experiments: it samples scrambles
for selected inputs. Quantifier order matters.

### An analytic reason the bulk decay is plausible

Here is a derived, unaudited argument for one fixed binary input. Let sorted
column sums be `s_1,...,s_n`, their mean be `mu`, and
`L = (1/n)*sum |s_c-mu|`. Let `p_r` be the fraction of columns whose sums
are at least row `r`. For fresh independent uniform row permutations, each
output column has mean `mu` and variance

`V = sum_r p_r*(1-p_r) = (1/(2*n^2))*sum_{c,d}|s_c-s_d| <= L`.

The equality follows by counting rows separating each pair of column sums;
the inequality is the triangle inequality through `mu`. Cauchy-Schwarz gives
`E[L_next | s] <= sqrt(V) <= sqrt(L)`. Initially the one-step variance is at
most `m/4`, so iterating conditional expectation and Jensen yields

`E[L_t]/m <= 2^(-1/2^(t-1))*m^(-(1-2^(-t)))`, for `t >= 1`.

This supports the proposed exponents without a Gaussian approximation or
independence between columns. It is only a fixed-input expectation bound.
It does not choose a single scramble sequence good for every input, does not
prove the fringe condition, and does not prove a cheap displacement repair.

### Depth arithmetic and obstacles

With `t` scrambles and full sorts, adjacent packs share the intermediate sort:
depth is `(t+1)*k*(k+1)/2` for `m=2^k`, and coefficient is
`(t+1)*k*(k+1)/4` under the existing scheduler.

Ignoring constants and uniformity losses, achieving bulk accuracy around
`2^-26` suggests `k` about 52, 35, 30, 28 for `t=1,2,3,4` respectively.
These give coefficients about 1378, 945, 930, 1015. These are optimistic
cost sketches, not bounds; the actual one-round proof needs `k=59`.
Multi-round bulk contraction with full sorts could offer a moderate reduction,
but these estimates do not support coefficient 200.

Even the existing fringe hypothesis alone forces `k >= 34` for power-of-two
columns. With that hypothesis unchanged, two scrambles with full sorts already
cost at least coefficient 892.5. No inference of an intrinsic barrier follows.

The shrinking typical displacement in Part B is more ambitious. To replace
later sorts cheaply, one needs a fixed comparator network that repairs a
precisely specified input class, and a guarantee that the preceding fixed
scrambles put every input in that class (or control exceptions). Typical
displacement for random scrambles and sampled inputs does not supply this.

## Recommended research sequence

1. Prove the finite conditional variance/L1 identities mathematically, then
   obtain tails for bulk errors, uniformly over relevant cuts.
2. Resolve the all-input quantifier: find a simultaneous witness argument
   or a deterministic invariant, accounting explicitly for the family of
   intermediate states. A naive union bound over all binary matrices is costly.
3. Analyze rare ranks separately; retain the present fringe primitive initially
   or replace its sufficient condition with a multi-round relative-error proof.
4. Only then design a comparator repair network for later rounds and charge
   its actual depth. This is the piece that could make 200 plausible.
5. If the required accuracy is the bottleneck, revisit the global stranger
   invariant and scheduler together, keeping local accuracy and depth explicit.

Verdict: multi-round simulation motivates a real fixed-input bulk lemma, worth
investigating. Full-sort repetition alone is not a convincing route to 200.
Uniformity, rare ranks, and cheaper later-round repair are separate obligations.
