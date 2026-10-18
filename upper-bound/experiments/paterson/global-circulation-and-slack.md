# Global circulation versus a weaker rebuild invariant

Status, 2026-10-10: informal structural arguments and exact rational parameter
accounting. No new network construction or improved coefficient is proved.

## Global circulation resolves counts, not oblivious routing

Assign each key its finest native interval. For each protected leaf `i`, let
`f(i,j)` count its keys native to leaf `j`. Off-diagonal counts describe
misplacement. Exchanges between bins can use these misplaced native keys as
replacement resources instead of requiring every bin to own an initially
pure reservoir. In a balanced assignment, misplacements decompose into
cycles; with unequal protected/native counts, the pool also supplies or
absorbs the resulting paths.

This is a value-set/flow statement. The counts and locations depend on input,
so a flow decomposition is not itself an oblivious comparator construction.
The following obstruction shows why a sparse direct cross-bin schedule is
not enough even in the simplest balanced case.

### Adjacent-rank swapped-pair obstruction

Take two equal blocks of `m` keys, with lower native ranks `1..m` and upper
native ranks `m+1..2m`. Swap ranks `m` and `m+1` between arbitrary positions
in the two blocks. Consider a network containing only comparisons between
the blocks, always sending the minimum left and maximum right, with no
internal comparisons and no additional pool.

Every such comparison is already ordered except the comparison between the
two swapped keys. Thus the input remains unchanged until that exact pair is
compared. An oblivious schedule that repairs every possible placement must
contain every one of the `m^2` cross-position pairs. A layer can contain at
most `m` disjoint comparisons, so depth is at least **m**.

The keys can be permuted internally initially; all other lower keys remain
less than all upper keys, so the argument is unchanged. It does not apply
once internal concentration moves the swapped keys or a larger auxiliary
construction is used.

This is a decisive barrier for *direct-only* global circulation. The earlier
native-reservoir expansion lemma avoids it only because it assumes enough
initially native replacement probes; balanced bins containing just the two
opposite misplacements do not satisfy that reservoir model.

### What a useful global construction would need

Internal extremal concentration defeats the singleton obstruction: the wrong
high key in the lower block is its maximum, and the wrong low key in the
upper block is its minimum. Two parallel tournaments followed by one comparison
can repair this rank-boundary classification in depth `ceil(log_2 m)+1`.
It need not restore each key's original physical position or finer bins.

For many contaminants, a promising but unproved interface is:

1. Concentrate opposite extreme cohorts into fixed boundary cores, retaining
   quantitative residual errors for all ancestor intervals.
2. Exchange or exactly partition the **union** of opposite cores, using their
   joint native-key counts rather than independent per-bin probe supplies.
3. Prove that errors introduced at finer cuts remain within their budgets.
4. Route outputs with explicit comparator depth and error accounting.

This is a stronger target than searching for cross-bin matchings. It also
avoids treating the pool's lack of individually certified native windows as
a proof that global native resources are absent.

## A count-feasibility reserve for protected finest purity

Let `W=N/16=n4+Q` be a leaf's destination width. Its actual upper-region
native-key count is `W+g_hi-g_lo`, at least `W-D_hi-D_lo`.
To certify that a protected set of size `p=n4-c` can be made entirely native
by globally exchanging keys, a sufficient count condition is

    p <= W-D_hi-D_lo,
    c >= max(0, D_hi+D_lo-Q).

At leaves with two nonzero deepest-boundary bounds, use
`D_hi+D_lo <= (32/35)K`. The original pool-slot allocation upper bound is
about `.56304K`, so this conservative reserve can require roughly `.35125K`
protected wires to be moved into the pool. At the root-window endpoints,
the diagnostic using that optimistic slot bound is approximately 1,067,472
and 2,135,600 wires per such leaf.

Actual `Q` must be used to certify an instance; an upper bound on `Q` is not
a sufficient chosen reserve. These numbers diagnose the possible resource
scale, not a proof that every admissible input requires that many removals.
Endpoint and half-adjacent cuts have smaller discrepancy allowances.
Feasible cardinalities do not identify which wires to extract or realize an
oblivious exchange.

## Permanent weakening at fixed primitive support is tiny

The existing invariant has `mu=.0199`, while its separator support is `.02`.
Raising the global error scale by increasing `mu` must maintain

    new_mu < .02,
    new_mu/old_mu < 200/199 = 1.0050251256...

This leaves less than 0.503% permanent headroom at fixed primitive support.
A larger enlargement requires a new supported primitive, or a changed
allocation/scheduler contract. Increasing `delta` can enlarge ancestor-error
budgets, but changes tail, rounded transition, deep purity, and root bounds;
it does not enlarge the first-stranger budget controlled by `mu`.

## Temporary root slack: rounded-source accounting

A separate root-only weak invariant could accept larger errors and restore
the ordinary invariant in the next comparison phase. It does not follow
automatically from enlarging `mu` globally.

For a diagnostic linear model, scale inherited `mu`-dependent stranger terms
by `gamma`, leaving fresh arrivals and rounding unchanged. The current
rounded first-stranger source estimate would become

    gamma*mu*(2 delta A + e/A)
      + (1-alpha+beta)/(2A) + rho/M <= nu*mu.

Using the existing parameters gives

    gamma <= 1.0055260504...

Only about 0.553% temporary inflation fits that source estimate. This is a
conditional scalar limit for this model, not a proved generalized transition
theorem or an impossibility bound for every weaker invariant. Its derivation
must be checked against the actual source terms before formalization.

For `gamma=2`, the same model requires `nu >= .8819231705`. Keeping `A=4.75`
would then yield stage ratio at least about **17.9171**, compared with the
current 6.5 certificate. At separator cost 989 this is a major deterioration,
regardless of a moderate root-repair saving. The capacity identity would
require a larger fringe parameter too. This is not a feasible full parameter
instance until every interior, allocation, and purity condition is checked.

The arithmetic is reproducible in `circulation_slack_budget.py`. Rational
inequalities are exact; the reported real stage ratio is numerical only.

## Assessment

Neither simply adding slack nor a direct cross-bin exchange graph provides
a demonstrated improvement. Current parameters have too little cheap error
headroom, and global circulation needs internal concentration before sparse
exchanges can be effective.

The most concrete next target is **paired boundary-core concentration and
repair**, starting with two adjacent native intervals and tracking both error
directions. Its crucial new lemma should use the combined core's rank counts
to repair sparse contamination without assuming independent pure probes.
Before scaling to sixteen bins, check that one boundary operation preserves
the ancestor error budgets and account for the scheduling of overlapping
boundaries. The singleton tournament construction gives a real base case;
the many-contaminant and overlapping-boundary cases remain research obligations.
