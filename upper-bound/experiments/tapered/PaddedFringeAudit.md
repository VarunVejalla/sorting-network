# Fringe padding audit

## Status

`PaddedFringe.lean` contains ordinary conditional padding transfer and the
baseline-row identities described below. `BaselineFringe.lean` proves both
high- and low-fringe bridges with genuine multiplicative `(1/P.J)*j` error on
the restricted live register, assuming the corresponding truncated SR/R1/R2
witnesses. The low-side proof reverses the full physical pack, applies the
baseline argument to the flipped truncated scrambles, then transfers the
lowest-`j` event through prefix restriction; it requires the protected fringe
to fit inside the requested suffix, with no padding allowance. The provider
exposes this as `TruncatedPaddedWitness.fLow_baseline`. Focused Lean checks
pass. These remain local results, not a completed outsider invariant or an
asymptotic sorting theorem.

## Why ordinary F padding is insufficient

Let the rectangle size be `A=a+p`, with `p` dummy ranks at the end. The
largest `j` live ranks are the largest `j+p` padded ranks after excluding
dummies. The direct physical F estimate therefore gives
`epsF*(j+p)`, not `epsF*j`. The low side keeps the original cohort `j`.

This additive error cannot simply be charged to a scalar reserve when the
induction requires higher-order budgets such as `mu*delta^r*C`: these shrink
with `r`, while the padding charge does not.

There is a genuine black-box obstruction. On `A=a+1` wires, compare each
live wire `i<a` once with the last wire `a`. The maximum is then at the last
wire. With protected suffix length `F>=2`, `J=2`, and `epsF=3/5`, all inputs
satisfy the high F estimate: zero escapes for `j=1`, at most one escape for
`j=2`, and `1<6/5`. Restricting to `a` wires deletes every comparator. The
restricted identity network can leave the largest live key outside its
protected suffix, violating `1<3/5`. Thus universal multiplicative transfer
cannot follow from the ordinary full-network F contract alone.

The issue persists for small errors. An insertion-selection network can
maintain the largest `K` keys in `K` final wires using only comparators
incident with those final wires. Full high F is perfect for every `j<=K`;
padding those `K` wires and restricting removes every comparator. This
example concerns a generic F contract, not the particular pack construction.

## Proposed direct pack repair: one full baseline row

The nearby rectangle has padding strictly below one row. All dummy inputs
lie in its final input row. For the largest `j` live cohort, augment the
Boolean threshold input by marking **every** cell of that final row. This
dominates the actual padded threshold input.

After the first column sort, each column has at least one marked cell.
Remove one marked bottom cell per column. The residual total is at most
`j`, because the augmentation added the entire bottom row and may only
discard live cohort marks already in that row.

For any residual monotone column heights `c` on `m-1` rows, define lifted
heights `c+1` on `m` rows. If `sigma'` is `sigma` restricted to its first
`m-1` rows, then exactly

```
scrambledColSum (c+1) sigma = scrambledColSum c sigma' + 1
onesAboveBottom (c+1) sigma (f+1)
  = onesAboveBottom c sigma' f.
```

The final row is completely marked, so its scramble supplies exactly one
mark to every column. Column sorting preserves this baseline. The identity
therefore iterates through both rounds without additive errors.

Apply the existing deterministic F2 reduction to the truncated scrambles
and residual mass at most `j`. A protected full fringe of `f+1` rows then
inherits a genuine multiplicative `epsF*j` estimate. Choose
`(f+1)*n <= u`, where `u` is the actual half-up wire count; the desired live
unprotected region is contained in the rectangular unprotected region.
The low side can retain its ordinary full-rectangle flipped F guarantee.

## Deterministic bridge: now checked

1. Boolean semantic execution is monotone under input domination.
2. The filled-bottom-row initial column sort has residual total `<=j`, proved
   for actual padded permutation thresholds by injection into `[a-j,a)`.
3. The one-round baseline identity iterates through the two-round height
   decode. The pure-column F2 reduction tolerates total residual mass `<=j`.
4. `paddedPack2Net_fHigh_baseline` transfers the bound to actual restricted
   physical output, preserving `epsF*j` with no dummy cohort surcharge.
5. The symmetric low-side estimate follows by `physicalPack2Net_flip`, using
   the flipped truncated witnesses and the fact that suffix dummy ranks are
   all at least `a`; `paddedPack2Net_fLow_baseline` is kernel checked.

## Remaining integration

1. **Closed:** `TruncatedScrambleMeasure.lean` proves exact failure-fraction
   preservation under truncation, and `TruncatedFringeProvider.lean` combines
   SR/R1/R2n on the retained rows with actual full-rectangle B2 witnesses in
   both flip orientations. `TruncatedPaddedProvider.lean` packages one actual
   rectangle and the same scrambles with all these contracts.
2. Instantiate the local integer flow and padded witness together at each
   active scheduled bag, and check the cohort range `j <= deltaF*f*n`. The
   low-side fit arithmetic now follows from the address-debt bound, one-wire
   up-flow rounding, and the 69-wire occupancy invariant. No padding
   enlargement of `j` is needed.
3. Match both rare-rank orientations to the actual ragged slot profile and
   derive each stage's input tails from the outsider invariant and schedule.
4. Feed this genuine two-sided rare-rank interface into the higher-order
   outsider transition, rather than the weaker additive-padding theorem.

The deterministic baseline argument and simultaneous witness existence are
kernel-checked. The complete recursive outsider propagation remains open.
The argument avoids the black-box obstruction by using the pack's
row/column structure directly.
