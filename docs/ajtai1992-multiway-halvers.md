# Ajtai–Komlós–Szemerédi 1992 multiway-halver lead

Research note, 2026-10-10. This records the claims in
[ajtai1992.pdf](ajtai1992.pdf), their possible connection to the checked
Chvátal construction, and the proof obligations for using them. No improved
sorting theorem is claimed here.

## What the paper proves

The paper changes the primitive from a binary comparator to a k-sorter,
which sorts k selected positions in one unit of delay. A k-network layer is
a partition of the wires into disjoint k-sets, with a k-sorter on each set.

Theorem 1 (page 688) says that for k >= 23,

    epsilon = c0 * sqrt(log(k) / k),
    c0 = 3 for k >= 23, and c0 = 2 for k >= 60.

For every N >= 23, there is a depth-two k-network on kN wires that is an
epsilon-halver. The first layer sorts the k columns of the row-major k by N
matrix. The second layer uses a fixed permutation of the entries within rows,
then sorts the resulting columns. The theorem quantifies over all inputs; the
permutation is selected by a probabilistic existence argument. The proof
sketch counts monotone 0-1 matrices and bounds the failure probability of a
random permutation (pages 690-692).

The error depends roughly on k^(-1/2), up to the logarithmic factor. Since
k-sorter layers can be simulated by binary sorting networks on k inputs, the
local binary depth is twice the depth of the selected k-sorter. With Batcher
bitonic sort this is quadratic in log(k); with a stronger small sorter it can
be lower. The paper says this gives an ordinary-network halver whose error
decreases exponentially with its depth, while warning that the constant may
be large.

There is a second, less formal multiway claim on page 687. Immediately after
describing the two-round construction, the authors say that it is a good
halver and that “even partitioning into about `sqrt(k)` parts has been done
quite accurately.” This is an assertion about the same construction, not a
corollary stated with a definition or numerical error bound. In particular,
the paper does not say whether “accurately” means a bound at every one of the
`p-1` output cuts, how the bound depends on the input rank, or how it composes
when the pieces are combined. It is evidence that the construction was meant
to have multiway behavior, but it is not yet a usable multiway theorem.

The final remark (page 689) proposes going directly to a p-way near-sorter:
split into k*p^2 parts, use two rounds of the k-sorter construction, then
combine parts into a good p-partition. This is presented as a route to
“drastically” improving the AKS binary-comparator constants, with p = 16 or
32 suggested. The cited reference is Ajtai, Komlós, Paterson, and Szemerédi,
k-sorting, “in preparation.” This paper does not state a binary sorting
depth coefficient of 60-100 or prove the end-to-end improved AKS sorter.

These are two distinct claims: page 687 reports an observed/argued
`sqrt(k)`-way accuracy for the two-round `k x N` construction, while page 689
sketches a proposed construction for a chosen `p` using `k*p^2` initial parts
and an unspecified combining step. The paper does not establish that the
second follows from the first, nor identify the error parameter needed for
either one. Theorem 1's `epsilon` controls only the central two-way cut.

## Why this is relevant to the checked 1770 endpoint

The current Chvátal implementation has ordinary-stage depth 3540: two
parallel column-sort rounds, each budgeted at 1770 binary layers. The global
network uses three ordinary stages for every factor-64 increase in size, so
the leading coefficient is 3*3540/log2(64) = 1770.

The current local rounds sort columns of size 2^59 exactly using bitonic
networks; see AKS/Chvatal/SeparatorDepth.lean. The 1992 proposal could matter
by replacing these exact, very deep local sorts with approximate multiway
partitioning and an error-recovery schedule. Its two-layer halver alone does
not provide that schedule or the required multiway separator contract.

The existing Lean code gives the required contract precisely. For a node with
row count m, column count n, parent fringe f, and child block size b, the
network `physicalPackNet m n hn σ` must satisfy `NodeSpec` in
`AKS/Chvatal/NodeSpec.lean`. Its bulk clauses bound leakage at all 65 cuts
`π/2 + j*τ`, j = 0,...,64, where `π = 2*f*n` and `τ = b*n`. Its fringe
clauses bound leakage of the extreme j keys by `eps*j`, for every
`j <= floor((128/4095)*(π/2))`; here `eps = 1/(86*10^6)`. The derived
`HasPackSemanticPropertyB` and `HasPackSemanticPropertyF` in
`AKS/Chvatal/MatrixBridge.lean` are convenient sufficient input-side
contracts. Node geometry has `2^58 < m <= 2^59` and `n >= 16`.

This makes the gap exact: Theorem 1 of the 1992 paper is a central halving
guarantee for one cut. It does not imply the 65-cut bulk clause, nor does it
directly control the fringe leakage region in `NodeSpec`. The direct p-way
near-sorter sketched on page 689 is the relevant missing ingredient. A first
formal target should therefore be one node network satisfying `NodeSpec`
with an explicit binary depth, not merely formalizing the central-halver
statement. The paper's theorem also assumes N >= 23, while current node
geometry allows n as small as 16; padding or a separate finite construction
would be needed if the p-way theorem retains that restriction.

For scale only, if a compatible replacement preserved the current three
ordinary stages per factor-64 growth and achieved binary ordinary-stage depth
T, its leading coefficient would be T/2. A coefficient below 100 would
therefore require T < 200. This is a scheduler budget, not a bound proved by
the 1992 paper. Inserting its halver theorem into the existing stage without
proving all rank, orientation, fringe, and repair conditions would not justify
this accounting.

The depth-only scale is instructive, but it hides the main obstacle. For
k = 2^r, Batcher's bitonic sorter has depth r(r+1)/2, so two k-sorter layers
cost r(r+1) binary layers. If that were the entire ordinary stage, the current
global accounting would give coefficient r(r+1)/2: 91 at k = 2^13 and 105 at
k = 2^14. But the paper's halver error at these arities is around 5–8%,
depending on its logarithm convention. The current `NodeSpec` tolerances are
about 10^-8. Thus these depth figures cannot be substituted into the current
scheduler. Reaching that coefficient range requires the direct p-way
construction to support a different global error budget; that argument is
absent from this paper.

## Proof obligations for a usable construction

1. **Recover the precise multiway contract.** Formalize the two-layer halver
   including the fixed permutation, the error convention, both orientations,
   and the range of supported ranks. Then derive the proposed p-way near-sorter
   guarantee, including the combination step omitted from the paper's final
   sketch.
2. **Price the k-sorters in binary depth.** Choose actual binary networks for
   every k-sorter and prove their depths. Count all serial layers, including
   any finishing network. Represent each row permutation by its fixed
   one-factor comparator groups, as the paper specifies, rather than as an
   adaptive data movement operation.
3. **Connect the local guarantee to a global invariant.** State the exact
   error and rank bounds needed by a repeated bag or tree schedule. Prove that
   errors remain repairable across all stages, including partial bags and
   terminal blocks.
4. **Account globally before formalizing the full proof.** Optimize k, p,
   binary sorter depth, error rate, and the number of stages together. The
   relevant objective is the final binary depth coefficient after the global
   scheduler, not the depth of an isolated halver.
5. **Audit the historical 60-100 claim separately.** Chvátal reports it as a
   claim by Komlós, and Seiferas calls the 100 coefficient private. The 1992
   paper points to k-sorting in preparation. Locate a surviving copy or
   presentation notes and compare their exact parameters and model before
   treating either number as a theorem.

## Follow-up literature check

The named “k-sorting, in preparation” reference has not surfaced as a paper
under that title. Later literature does show that the broad k-sorter program
continued. Cypher and Sanz's *Cubesort* (1992) and Parker–Parberry's
*Constructing Sorting Networks from k-Sorters* (1989) give k-sorting
constructions; the 2024 paper *Towards Simpler Sorting Networks and Monotone
Circuits for Majority* surveys these and gives a polynomial-time construction
of depth `(2+o(1)) (log_k n)^2` when `k` grows faster than every polylogarithm
of `n`. It also explains the recursive interpretation: replace each k-sorter
with a smaller-arity sorter until reaching binary comparators. This establishes
that k-sorting is a live and useful line of work, but it does not state a
60–100 binary sorting coefficient or provide the missing 1992 p-way error
analysis. Its stated `(log_k n)^2` depth does not by itself yield a linear
depth binary sorting network by recursive substitution; that would require
additional structure or a stronger k-sorting result.

A separate 2017 paper repeats an approximate AKS constant of 6,100 while
citing Knuth. A 2024 survey instead describes the familiar Paterson/Seiferas
binary constants as above 1000. These are secondary statements with different
provenance and do not authenticate a 60–100 endpoint. The current evidence
therefore supports treating “60–100” as an unverified historical lead; the
concrete 1992 theorem remains the two-round one-cut halver plus an unproved
near-sorter sketch.

## What the 60–100 report actually says

Chvátal’s DCS-TR-294 gives the primary-source provenance. Its abstract and
Theorem 1.1 state the explicit, unpublished-AKS-inspired construction that
Chvátal could work out: binary depth at most `1830 log_2 N - 58657` for
`N >= 2^78`. Theorem 1.2 is a different measure: with arbitrary `M`-sorters
treated as unit-cost hardware, its depth is `(48+o(1))*log_M N + 115`, with
the asymptotic taken as `M -> infinity`. Afterword §9 says Komlós claimed
“around 60 to 100” instead of 1830 and “less than 10” instead of 48, then
states that Chvátal did not know how closely his construction matched what
Ajtai, Komlós, and Szemerédi intended. Thus the 60–100 and <10 figures are
reports of a private estimate, not theorems or a parameter table from which
we can reconstruct the construction.

The report’s §8 optimizes its own separator-tree analysis from 48 to
`24 + 16*sqrt(2) ~= 46.627` in the M-sorter theorem. Under explicitly stated
assumptions on that framework, it argues that this constant cannot reach
23.313 without a significant change of approach. This is a framework-specific
barrier, not a lower bound on sorting networks and not a refutation of
Komlós’s different proposal. The 2024 Seiferas retrospective likewise says
the sharp analyses remained conference sketches or unpublished technical
reports, with no journal exposition found.

The paired private estimates in §9 have a plausible numerical connection.
Suppose a construction sorted `N` wires in at most `c_M log_M N + O_M(1)`
layers of `M`-sorters, and each `M`-sorter were implemented by a binary
Batcher sorter. For `M=2^r`, the binary depth per `M`-sorter is
`r(r+1)/2`, so the resulting limsup coefficient would be
`c_M * (r+1)/2` in base-two logarithms. If `c_M < 10`, this expression is
below 60 at `r=11` and below 100 at `r=19`; intermediate arities give the
reported 60–100 scale. This is a derived conversion, not a recovered theorem.
The published Theorem 1.2 only states `c_M=48+o(1)` as `M -> infinity`, and
the private `<10` claim comes with no explicit `c_M`, finite arity threshold,
or additive term. Even if `c_M -> c < 10`, that asymptotic alone does not show
that `c_M < 10` for any `M=2^r` with `11 <= r <= 19`. The crucial missing
artifact is therefore likely a finite-parameter analysis of the proposed
multiway separator / M-sorter construction, not merely the asymptotic slogan.

For reference, the Batcher conversion at the boundary value `c_M=10` is:

| `M=2^r` | Batcher depth per M-sorter | binary coefficient at `c_M=10` |
| ---: | ---: | ---: |
| `2^11` | 66 | 60 |
| `2^13` | 91 | 70 |
| `2^15` | 120 | 80 |
| `2^17` | 153 | 90 |
| `2^19` | 190 | 100 |

These entries are strict upper targets only if the corresponding finite
`c_M` is strictly below 10. The theorem’s asymptotic statement does not locate
the first such `M`; obtaining `c_M` at a usable finite arity is the next
quantitative question. Chvátal’s §8 asymptotic obstruction (`c >= 23.313`)
does show that his published separator-tree framework cannot supply such a
limiting coefficient under its stated assumptions. It does not rule out an
isolated finite-`M` improvement, because §8 is an asymptotic argument, but
there is no published finite table supporting one.

For our project the gap is now sharper: reproducing Chvátal’s Sections 1–7
cannot recover the 60–100 target, because those sections are precisely his
1830 implementation and he disclaims equivalence to the claimed design. A
useful new lead must supply at least one missing artifact: the AKS/Komlós/
Szemerédi separator construction with finite parameters, its quantitative
all-cut guarantee, or a different global schedule that turns the 1992 p-way
partition into a sorter.
The current `NodeSpec` remains a good formal acceptance test for the first
artifact, but its present error tolerances and scheduler are calibrated to the
Chvátal construction and may need redesign for the private proposal.

## Suggested first technical milestone

The first test should make “good p partition” precise. Let a fixed network act
on `L` wires, with `p | L`, and feed it a binary input with `q` ones (ones
represent the largest keys). At output cut `s_j=jL/p`, the ideal sorted prefix
contains `max(0, q-(L-s_j))` ones. Define the cut leakage as the actual number
of ones in the first `s_j` output wires minus this ideal count. A finite
all-cuts p-way theorem should bound this leakage by a stated `E` for every
`q=0,...,L` and `j=1,...,p-1`, using one fixed network. This is a necessary
bulk contract; the Chvátal scheduler additionally needs its rank-sensitive
fringe estimates, and a differently designed schedule may need a different
contract.

Then prove the finite binary-comparator theorem for one p-way instance with
explicit `k`, `p`, `N`, depth, and this universal 0-1 guarantee. Use the
paper's row-permutation construction and counting proof, and make the
part-combination map explicit. Finally compare the measured `E` and depth to
the intended global schedule before formalizing it. This isolates whether the
1992 idea can reach a useful total depth at all.

The first reconstruction pass should test the smaller page-687 assertion
before attempting the page-689 `k*p^2` sketch: write down candidate all-cuts
leakage bounds for `p` near `sqrt(k)`, then check whether the published
two-way `epsilon` theorem and its counting argument actually imply them.
If not, the missing ingredient is a stronger multiway counting lemma (or a
separate AKPS result), not a bookkeeping corollary. For initial finite tests,
`k` should be large enough that `sqrt(k)` is in the suggested `p=16,32`
range; the proof must also account for `N >= 23`, divisibility/padding, and
the binary depth of every k-sorter layer and combination network.

Here is the precise 0-1 statement to test. For a fixed depth-two network on
`kN` wires, let `M'` be its output matrix after the final column sorts. At a
row cut `h` define

    leak_h(M') = #ones in the first h rows
                  - max(0, m - (k-h)N),

where `m` is the total number of ones. The subtracted term is the number of
ones that must lie in the prefix even in a perfectly sorted output. Thus
`leak_h` is exactly the number of excess ones above the ideal rank boundary
(equivalently, excess zeros below it). The central theorem controls this
quantity at `h=k/2`, up to the paper's `epsilon*m` normalization. The desired
multiway lemma is: find one permutation-vector `Pi`, independent of `M`, and
an explicit `E(k,N)` such that for every monotone input `M` and every
`h=j*k/p`, `j=1,...,p-1`,

    leak_h(S Pi M) <= E(k,N) * min(m, kN-m).

Using `min(m,kN-m)` states both orientations symmetrically. If the appendix's
proof only gives `E*m` for `m<=kN/2`, complementing zeros and ones gives this
form. A useful result must give a finite numeric `E` at `k=256,p=16` or
`k=1024,p=32`, not just `E=O(sqrt(log(k)/k))` with hidden constants.

The paper does not imply this lemma from Theorem 2 as written. Theorem 2
selects a permutation-vector that works simultaneously for every monotone
input and rank at the *single central cut*. Repeating its existence argument
for each `h` gives potentially different permutation-vectors. A union bound
over the `p-1` bad-cut events could produce one common vector, but the appendix
only establishes its probability estimates for `h=k/2`; its displayed
intermediate failure bounds (0.2 or 0.3 in the least favorable parameter
range) are too weak to union-bound over 15 or 31 cuts. This is a proof gap,
not a counterexample: stronger estimates at `k=256` or `1024`, or a joint
counting argument, could still make the simultaneous claim true. The sparse
input equivalence-class step (Appendix Lemmas 3–4) is where the dependence on
the cut location must be worked out; its parameter `d` is the distance from
the halfway threshold and cannot simply be reused unchanged for every `h`.

The exact random-variable reduction is simple and identifies the needed
generalization. For a fixed monotone input, let `X_j` be the number of ones
in column `j` after the row permutations and before the final column sorts.
Since those final sorts put ones at the bottom of each column, the number of
ones in the first `h` rows is

    sum_j max(0, X_j - (k-h)).

Hence `leak_h` is this sum minus `max(0,m-(k-h)N)`. For a fixed set of
columns, the total number of ones in those columns is a sum of independent
hypergeometric variables, one from each independently permuted input row.
That is exactly the distributional setup of Appendix §4.1. The individual
`X_j` need not be independent across columns, so a multi-cut proof must retain
the appendix's set-of-overfull-columns counting step rather than multiply
single-column tail probabilities as if they were independent.
For each fixed `h`, one should redo its dense-rank estimate and its sparse
equivalence-class estimate with the overflow threshold `k-h` (or use the
complementary zero formulation). This yields a candidate failure probability
`δ_h(k,N,E)` for the event that *some* monotone input violates the desired
leakage bound at cut `h`. A common permutation follows if

    sum_{h in {k/p, 2k/p, ..., (p-1)k/p}} δ_h(k,N,E) < 1.

The published central-cut analysis supplies the full `δ_h` only at
`h=k/2`. Appendix Lemma 4 can be specialized to handle a sparse rank range at
any target cut, as derived below, but the dense-rank estimates still need to
be redone. For `p=16,32`, the immediate task is to determine whether those
noncentral dense estimates make the total failure probability less than one
at the relevant finite `N`; the direct p-way sketch may require `N=p^2`, not
the theorem's minimum `N=23`.

The sparse-rank part of the all-cuts extension does follow from Appendix
Lemma 4. At a target prefix of `s` rows and rank `m=mu*N`, set `d=s-mu`.
Then the lemma's line `mu+d` is exactly row `s`; its rank condition
`mu <= d/10` is equivalent to `mu <= s/11`. Thus, whenever `d>=10` and
`E >= (2+log d)/d`, the lemma bounds the probability that any input of this
rank leaks more than `E*m` ones across this cut by `15*d*x/(1-x)`, with
`x=(e/10)^d`. For the complementary zero orientation, reverse the row order
and apply the same random-permutation argument. Sum these probabilities over
ranks and cuts. This is a specialization of the published sparse lemma,
using it separately at each rank-dependent `d`.

For the remaining ranks, both screens use a deliberately coarse count of
monotone inputs of weight `m` by the weak-composition bound
`binom(m+N-1,N-1)`. For a fixed set of `q` overfull columns, Appendix §4.1
gives a hypergeometric tail of at most
`exp(-2*Delta^2/(k*q))`, where

    Delta = t*q + max(0, m-t*N) + E*m - q*m/N.

If the threshold exceeds `m`, that event is impossible. Union-bounding over
the q-sets, remaining weights, all requested cuts, and both orientations gives
the screen in [`screen_multicut.py`](../upper-bound/experiments/ajtai-multiway/screen_multicut.py).
Numerically, its union-bound expression falls below one at `N=23` with
`E=0.55` and `E=0.45`:

| `k` | `p` | two k-sorter layers, Batcher binary depth | log10 failure upper bound | numerical screen |
| ---: | ---: | ---: | ---: | --- |
| 256 | 16 | 72 | -4.359 at `E=0.55` | below one |
| 1024 | 32 | 110 | -9.269 at `E=0.45` | below one |

At `E=0.50`, the `k=256,p=16` log10 bound is 8.242; at `E=0.40`, the
`k=1024,p=32` bound is 9.396. Positive log bounds do not show that such a
permutation fails; they only say this union bound cannot certify one. The
script uses floating-point arithmetic and is a research screen, not a
machine-checked or outward-rounded numerical certificate. The `E=0.55` and
`0.45` candidate bounds are still weak for a useful near-sorter and need a
global error schedule; they allow leakage of more than half the minority
mass for `p=16` and nearly half for `p=32`. These are finite numerical
candidate bounds for the two-layer network only;
they do not price the separate “combining the parts” operation in the page-689
`k*p^2` proposal. The two-layer Batcher depths correspond to hypothetical
coefficients 36 and 55 only if they replace an ordinary stage in the current
three-stages-per-factor-64 scheduler, before any combining or repair cost.

There is also a parameter mismatch to resolve before identifying these with
the page-689 proposal. The table uses the theorem's minimum `N=23`, so its
two-round networks have `kN` wires. The final remark instead starts from
`k*p^2` parts and then says to combine them. If those parts correspond to
`N=p^2` columns in the two-round network, the relevant finite instances are
`N=256` and `N=1024`, followed by the omitted combination. The `N=23` table
is a small-module test of the all-cuts lemma, not a depth analysis of that
direct p-way construction.

For the proposed `N=p^2` cases, [`certify_dense.py`](../upper-bound/experiments/ajtai-multiway/certify_dense.py)
now closes the dense-rank estimate with outward-rounded interval arithmetic
(`mpmath.iv`). It branches over the continuous rank `mu` and overfull-column
fraction `x`, which safely contains all discrete ranks and column counts. On
each box it bounds the weak-composition entropy at the rank endpoint, binary
entropy by its maximum on the x-interval, and the Hoeffding penalty from a
corner minimum of the bilinear excess `Delta`. Subdividing until every rate
box is below `-ln(2*term_count)/N` makes the entire dense-rank union sum at most
`1/2`. The script widens computed domain endpoints by `1e-10` and adds a
`1e-12` guard after conversion of interval endpoints to binary64.

It also sums the sparse-rank Appendix Lemma 4 bounds with interval arithmetic.
For `(k,p,N,E)=(256,16,256,.55)`, the dense and sparse failure bounds are
`0.357978261` and `0.000959285`, total `0.358937546`. For
`(1024,32,1024,.45)`, they are `1.73e-17` and `9.18e-11`, total
`9.18e-11`. Both are below one, so under the paper's stated counting and
hypergeometric inequalities the probabilistic argument yields one fixed
row-permutation vector that works simultaneously for every monotone input and
every requested cut, with leakage at most `E` times the minority mass. This
is a finite all-cuts existence result for the two-round k-sorter core at these
parameters. It is numerically certified, not Lean/kernel checked; the
interval script and the reduction from Appendix 4.1 remain subject to
independent review. The older sampled-rate outputs remain diagnostic and are
no longer the basis for the dense-rank bound.

For comparison, the paper's one-cut formula `2*sqrt(log(k)/k)` at these two
arities is approximately 0.29 and 0.16 with natural logarithms, or 0.35 and
0.20 with base-two logarithms. Those central-cut guarantees are better than
the finite all-cuts leakage fractions established here. The coarse
weak-composition count suffices for the finite existence screen after the
interval argument; the remaining obstacle is converting this local result
into a useful global sorter with much smaller accumulated error.

## What can and cannot be reconstructed about combining

The paper's final paragraph does not define the “combine parts” network, its
interface, or its depth. The cited Parker–Parberry paper does give a general
way to build full sorting networks from `k`-sorters, but its stated cost is
quadratic in `log_k n` layers of `k`-sorters (plus binary mergers), so it does
not fill in the missing shallow local p-way combination required by the AKS
sketch. It is a useful correctness template for treating each part as a
sorted block, not evidence for the proposed shallow combiner. [Its abstract
and bibliographic record](https://doi.org/10.1016/0020-0190(89)90196-8) state
the sorter and merger costs explicitly.

The two-round, all-cuts core is now numerically certified at `k=1024`,
`p=32`, and `N=p^2=1024` with leakage fraction `E=.45` at all 31 cuts; two
Batcher-simulated sorter rounds cost 110 layers. The `(256,16,256,.55)` core
also has a total failure bound below one and costs 72 layers. These are
meaningful finite local results, but `.45` and `.55` leave almost half of the
minority mass misplaced. It does not meet the current Chvátal `NodeSpec`
tolerances or the 107-layer central-repair budget. No global schedule follows
from it. The missing combiner must be specified and shown to reduce/combine
these errors at an affordable depth, or a new global invariant must tolerate
this much leakage. The existing work gives no such construction, so the 60–100
binary coefficient remains unverified.

The natural first parameter probes are `(k,p)=(256,16)` and `(1024,32)`.
With Batcher bitonic k-sorters, the two explicitly described k-sorter layers
would cost `2 * r(r+1)/2 = r(r+1)` binary layers, namely 72 and 110. Under
the current three-stages-per-factor-64 accounting these alone correspond to
coefficients 36 and 55. These are only lower-level budget probes: they omit
the unspecified combining operation, any extra rounds needed to get all
`p-1` cuts, and global error recovery. The page-687 theorem's one-cut error
at these arities is also far too coarse to substitute directly for the
current `NodeSpec`; the point of the probe is to find out whether a distinct
multiway contract and schedule are plausible.

## Sources

- M. Ajtai, J. Komlós, E. Szemerédi, “Halvers and Expanders,” FOCS 1992,
  pp. 686-692. Local copy: [ajtai1992.pdf](ajtai1992.pdf).
- N. Dobrokhotova-Maikova, A. Kozachinskiy, V. Podolskii, “Towards Simpler
  Sorting Networks and Monotone Circuits for Majority,” APPROX/RANDOM 2024,
  [paper](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2024.50).
- R. Cypher and J. L. C. Sanz, “Cubesort: A parallel algorithm for sorting N
  data items with s-sorters,” *Journal of Algorithms* 13(2), 1992,
  [DOI](https://doi.org/10.1016/0196-6774(92)90016-6).
- B. Parker and I. Parberry, “Constructing Sorting Networks from k-Sorters,”
  *Information Processing Letters* 33(3), 1989,
  [DOI](https://doi.org/10.1016/0020-0190(89)90196-8).
- V. Chvátal, “Lecture Notes on the New AKS Sorting Network,” DCS-TR-294,
  1992, especially §§8–9; [Rutgers record and report](https://doi.org/10.7282/T379487B).
- J. Seiferas, “Sorting Networks of Logarithmic Depth, Further Simplified,”
  Algorithmica 53 (2009), 374-384; corrected exposition dated 2017,
  especially its discussion of the unpublished sharper analyses.
