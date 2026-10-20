# UB-41: persistent columns and receive mixing

Date: 2026-10-20. Author: Codex (GPT-6). Status: small-C all-profile
recurrence refuted; stronger variants parked. No improved bound or Lean.
Worktree `.claude/worktrees/sub300`,
branch `sub300-structural`, starting at main `5f03290`.

## Objective and acceptance gates

Prove limsup D(n)/log2(n) <=300. The accepted endpoint is 789.75. Keep this
work independent of the root-checkout UB-34/UB-37 fringe work. Lean comes
after an explicit algorithm, uniform rank proof, terminal condition, complete
depth account, and fresh-context review.

The promoted R1 scheduler has a useful existing terminal condition: its
geometrically decaying outsider invariant implies that the final bags contain
their exact native rank intervals; parallel exact sorting then finishes.
We aim to retain this condition, rather than infer sorting from aggregate
profile error. Current R1Point cannot achieve300 merely by changing numbers:
its small-sender exact-sort interface forces stage depth >=759, hence
coefficient >=569.25. A new promised provider and integration are required.

## Proposed operation (aligned interior model first)

Each live bag is an m-by-n rectangle with columns sorted. Logical ordering is
row-major. A port is a prescribed contiguous row slab (the up-port may use
both end slabs). Source and receiving column counts may differ. For a source
with n_s=d_s*n_v columns, independently permute its n_s entries in each port
row, then distribute d_s entries to each of the n_v destination columns.
Combine the source pieces and sort each receiving column. Fixed permutations
are permitted in the generalized network, with final untangling only after
the all-input sorting proof. They are never data-dependent.

The actual dimensions, fractional rows, n_s<n_v cases, padding, endpoints,
and all frontiers must eventually be specified. The present algebra is only
for the aligned interior case; it is not an executable all-n scheduler.

For one Boolean threshold, source columns have prefix heights h_s,i.
Let p_s,r be the fraction of columns whose height exceeds r. An output count
is exactly the sum of the selected row indicators. Its mean is the actual
total arriving threshold count divided by n_v: there is no presumed
source-target averaging law. With independent random row permutations, for
a FIXED input profile its variance is at most

    sum_s d_s * sum_(r in selected port) p_s,r*(1-p_s,r).

The profile dispersion W_s=sum_r p_s,r*(1-p_s,r) equals
sum_i,j |h_s,i-h_s,j|/(2*n_s^2), and is bounded by the mean absolute
height deviation e_s. Thus the fixed-input expected output deviation is at
most sqrt(sum_s d_s*e_s). For the nominal interior capacity geometry,

    D = sum_s d_s = k*A/nu + 1/(A*nu).

At (k,A,nu)=(16,32,1/8), D=4096.25. This fixed-input expectation is NOT a
uniform all-input network guarantee: a suitable deterministic schedule
certificate or adversarial probability bound remains essential.

An internal random row scramble followed by another column sort would have
the analogous fixed-input estimate with D=1. If a UNIFORM promised-input
theorem with coefficient C were available, r total receiving/internal sorts
suggest the conditional fixed-point scale

    e_* = C^2 * D^(1/(2^r-1)).

This recurrence is a screening hypothesis. It has not been proved uniform
over adaptively chosen profiles, repeated stages, or all Boolean thresholds.
Do not use it as a new tolerance multiplier in the global invariant.

## Required correctness interface

1. Simultaneous threshold column-dispersion control on all reachable profiles,
   including a deterministic bootstrapping stage.
2. Both-direction all-cut bounds: sorted column heights with mean absolute
   deviation e give leakage <=n*e/2 at a row-aligned true-rank cut. Charge
   partial rows and padding separately.
3. Multiplicative rare-fringe control for every supported cohort size. Small
   average deviation alone is insufficient. Test minimal prefix-profile cost
   needed to concentrate >f keys into an output column; include dependencies
   across stages. A one-key fringe observation is not a terminal proof.
4. Actual port dimensions and generalized packet/rank support propagation,
   then promised-provider versions of R1Specs/R1StageKernel as needed.
5. Reuse the checked global outsider induction and exact final purity if the
   preceding contracts truly match it. Reprice the schedule for any new
   exponent parameters; current promoted rate is3/4 stages per binary log,
   not the historical Chvatal1/2.

## Initial bounded experiment

Screen a conditional bulk-only depth budget against the design-P scalar
constraints for r=1,2,3 sorts and several hypothetical uniform constants C.
Do not treat deletion of the fringe floor as a construction. Failure of this
sufficient model is a prioritization screen, not an impossibility bound. If a point passes,
derive the uniform theorem and sparse-fringe witness cost and have a fresh
reviewer attack them before any Lean.

Result: `REVIEW.md` also gives a deterministic first-row counterexample to the
small-C uniform recurrence itself: at the displayed point C must be at least
15.9961, rather than1. `FRINGE-WITNESS.md` gives a counterexample to the weak
dispersion-only fringe promise at the displayed295.167 point. A fresh review
confirmed its algebra and scope; see `REVIEW.md` and `STATUS.md`. The one-pass
variant is parked. A fixed-radius closure theorem is a distinct, untested
possibility; neither counterexample disproves all reachable-state variants.
No improved sorting coefficient follows from the screen.

## Excluded shortcuts

- The earlier UB-25 fixed matching/rounding recurrence did not imply terminal
  sorting; a positive aggregate steady state does not supply final purity.
- Zig-zag Sort (Goodrich2014) has linear-size serial sweeps and is not an
  O(log n)-depth drop-in: the author's arXiv1403.2777, page2 footnote1,
  explicitly distinguishes its time/size result from AKS depth.
- Existing UB-37 periodic/tolerance models do not prove a restoration
  invariant and cannot be reused as established error tolerances.
