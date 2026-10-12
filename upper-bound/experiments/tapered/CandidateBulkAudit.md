# Candidate bulk existence audit

Current status: the probability assembly is complete and kernel checked in
`CandidateBulkWitness.lean`, `CandidateBulkFail.lean`, and
`CandidateBulkProvider.lean`. The sections below retain the historical proof
construction and identify the issues that were closed; do not read their old
“missing” wording as current status. The actual remaining separator gate is
the recursive outsider/suffix-size induction that uses the padded pack. The
truncated F2 probability gate is closed by `TruncatedScrambleMeasure.lean`,
`TruncatedFringeProvider.lean`, and `TruncatedPaddedProvider.lean`.

The 945 candidate needs two-round bulk error `epsB=2^-21` for every
`m >= 2^34`, `n >= 16`. Existing best proves a different numerical window,
using one-tailed union bounds. It cannot supply this provider by changing
constants in its existence wrapper.

## Reusable checked components

- `Bulk2Count.variance_le_of_excess`: exact-mass variance bound.
- `Bulk2Count.lemma63BernsteinBound`: parameterized per-state/per-subset tail.
- `Bulk2Elem.bernoulli_mgf_bernstein`, the row MGF, and Markov counting.
- Semantic two-round decoding, exact key-threshold mass, and flip pigeonhole.
- `CandidateBulkExistence.bernstein_half_columns`: when the witness has at
  most half the columns, the Bernstein exponent is
  `K = lambda*epsB/2 - lambda^2*(1/2+2*lambda/9)*E1/2`.

## Missing structural lemmas

Update: `CandidateBulkWitness.lean` now proves items 1 and 2 below,
including the actual scrambled-column complement identity, the small
two-tailed excess witness, and exact-mass/excess preservation under state
complementation. Probability counting/union assembly remains unfinished.
The complemented threshold can be zero when the original threshold is `m`;
permit zero in the cell union or discharge its empty positive-tail event.

1. Define the complemented column state `cbar j = m-c j` and the row-reversal
   bijection on scrambles. Prove its scrambled column sums are the complements
   of the original sums, and that the transformation preserves cardinality.
2. At exact mass, replace any positive excess witness on more than half the
   columns with a positive zero/complement witness on its complementary set.
   This is the actual source of the improved factor 1/2.
3. Round one: introduce an **exact-mass** predicate, rather than the existing
   `total <= n*i` pipeline predicate. Prove its two-tailed Hoeffding union bound,
   exponent `E1^2*m*n`. The old weaker mass premise prevents this reduction.
4. Round two: adapt `failBoundB2` using the two witness orientations and
   `bernstein_half_columns`. Union over states and column subsets, without
   an independent threshold index (exact mass determines it).
5. Apply the failure factors and combine with the independently required
   first-round F property. Decode to `HasPackSemanticPropertyB2`, then apply
   the pair/flip pigeonhole. Neither rate arithmetic nor a one-state tail
   asserts existence of a universally good pair of scrambles.

## Numerical specialization

Take `E1=38/10^6`, `lambda=1/80`, floor `M=2^34`.
The tight logarithmic bound uses
`log(2(m+1)) <= 35 log 2 + m/M - 1 + 1/M`.
Both candidate exponent gaps exceed `1/2` for every `m>=M`, so at `n>=16`
their basic union factors are at most `exp(-8)`, already below `1/1000`.
This has slack for an additional factor two for tail orientation. Use that
budget explicitly rather than assuming the two-tailed union has no cost.

The physical cost remains three column sorts at row floor `2^34`, hence the
candidate's `3*T(35)=1890` per ordinary stage. The probability improvement
changes the row floor; it does not reduce the number of sorts.

## Completed probability assembly

`CandidateBulkFail.lean` now checks the complete exact-mass two-tailed unions
for both rounds, their failure fractions, actual semantic decoding, and
`candidate_bulk_pair_exists`: for every `m>=2^34`, `n>=16`, a pair exists
with actual semantic B2 error `2^-21` in both flip orientations.

`CandidateBulkProvider.lean` adds independent auxiliary contracts on both
scrambles, each with failure share `F` satisfying `F+1/1000<1/2`, and the
actual padded B-only separator at depth at most 1890.

**Status:** the candidate B2 existence proof is complete. Actual compatible
F providers, recursive invariants, scheduling, and the complete sub-1000
sorting theorem remain separate obligations.
