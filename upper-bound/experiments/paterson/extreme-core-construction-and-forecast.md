# Concrete extreme cores and the global-bound forecast

Status, 2026-10-10: informal network construction using the existing
kernel-checked entropy-halver family, with exact rational depth-formula
certificates in Python. The adapter/correctness and global integration are
not formalized. No production files or sorting bounds are changed.

## Supported extreme-core construction

The four-block epoch needs support

    sigma = 2*mu = 199/5000 = .0398

of the original block's inputs, and relative error `epsilon=1/8` for the
conservative `5 epsilon` epoch contraction.

For a block of size `m` divisible by 32, select a depth `t`, between 1 and 4.
To construct a largest-key core, run a restricted halver on the block, retain
its upper half as the active block, and repeat only inside that active half.
The smallest-key core is symmetric. The final fixed core has `m/2^t` wires.

At stage `i=0..t-1`, the active block has size `m/2^i`. Set the halver's
supported parameter and stage error to

    alpha_i = 2^(i+1)*sigma,
    e_i = epsilon/t.

The supported rank count `alpha_i * (active size/2)` equals `sigma*m`, so
every surviving part of every original extreme cohort `j<=sigma*m` is covered.
Its survivors remain an extreme cohort of the active block. At stage `i`,
at most `e_i*j` original cohort keys can leave the active block. The total
loss is at most `(sum e_i)*j=epsilon*j`.

Thus this is an all-supported-rank core contract, not merely a bound for
the maximum cohort. All stages satisfy `alpha_i<=1`; for four stages the
last parameter is `.6368`. Left largest-key and right smallest-key cores
can be constructed in parallel. Sorting their union with the left core's
fixed quota supplies the asymmetric pair contract derived in the epoch audit.

No virtual odd-size keys are needed for this divisible-by-32 arity model.
General temporary block cardinalities still require an arity adapter. These
are fixed comparator compositions selected from existing existence families;
they do not inspect rank thresholds or choose comparisons based on input.

## Certified scalar cost table

`extreme_core_cost.py` uses rational logarithm intervals to certify every
entropy ceiling. For block size at most 305,532,147, it obtains:

| Stages | Core fraction per side | Stage depth ceilings | Concentration depth | Joint bitonic sort | Pair budget | Three-phase epoch |
|---:|---:|---|---:|---:|---:|---:|
| 1 | 1/2 | 13 | 13 | 435 | 448 | 1344 |
| 2 | 1/4 | 24, 27 | 51 | 406 | 457 | 1371 |
| 3 | 1/8 | 36, 39, 45 | 120 | 378 | 498 | 1494 |
| 4 | 1/16 | 47, 51, 59, 81 | 238 | 351 | 589 | 1767 |

These are sufficient implementation budgets, not lower bounds for every
possible primitive or an optimal error allocation. Smaller cores save sort
layers but require more accurate halver stages. In this concrete family,
equal per-stage error allocation does not produce a cheaper epoch than the
single-stage candidate.

The existing 1/32 separator fringe cannot meet this new support/error
contract even with unbounded depth: it must hold at least
`(1-1/8)*.0398*m=.034825*m` keys, exceeding `m/32`. This explains why simply
changing constants in the old small-fringe construction is insufficient.

## What the epoch budget does and does not accomplish

The conditional four-block contraction is 5/8 per epoch. This costs at most
1344 layers using the cheapest displayed implementation, **before** covering
all sixteen bins, root/cold storage, global deep-prefix discrepancies, and
final allocation. Multiple epochs cost correspondingly more.

Consequently these sufficient budgets do not certify a cheaper replacement
for the complete 561-layer root-region sort. The construction is useful for
isolating the cost problem, but is not a production improvement. The dominant
cost is exact combined-core sorting, not the single sparse halver.

The 13-layer halver cannot replace the 989-layer interior separator: its core
has half-block size and it omits the large-cohort fresh-stranger routing and
scheduled-fringe contracts. Enlarging the interior fringe also changes the
capacity identity and stage factor. This distinction is essential when
forecasting a global coefficient.

## Concrete global numbers

With the current Paterson comparison scheduler unchanged, the conditional
coefficient is

    C = 6.5*989 + r + 1 = 6429.5 + r,

where `r` must be the cost of a complete root repair, not just one pair or
epoch. Therefore:

| Complete root cost | Paterson coefficient | Status |
|---:|---:|---|
| 561 | 6990.5 | Existing completed legacy theorem |
| 300 | 6729.5 | Hypothetical budget; no complete repair constructed |
| 0 | 6429.5 | Accounting floor with the comparison schedule fixed |

The best checked repository coefficient remains **1770**, supplied by the
separate Chvatal package. A modest successful Paterson root improvement would
still be in roughly the 6500–7000 range and would not beat that endpoint.
The construction audited here supplies no justified improvement even to
6990.5 yet.

**Forecast:** there is presently no evidence-based numerical forecast below
1770 from this route. If we merely optimize root repair and keep the existing
interior comparisons, below 6429.5 is impossible within that accounting.
Reaching 1000 or 200 requires a separately proved major reduction of the
interior separator cost or a different global scheduling theorem, in addition
to any root improvement. The local 5/8 contraction is not such a theorem.

## Research decision

Do not invest in formalizing the entire four-block epoch as a claimed upper
bound improvement with these budgets. The useful next cost target is exact
**paired-core selection/merging** that avoids a full bitonic sort, preferably
with structure produced by concentration rather than arbitrary unsorted cores.
Its cost must be audited before the global scheduler work proceeds.

If the objective is an actual improvement of the current 1770 endpoint,
this Paterson route should remain exploratory until it also supplies an
interior separator/scheduler budget competitive with Chvatal. The concrete
arithmetic now makes that gap explicit.
