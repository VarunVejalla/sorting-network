# UB-24: signed prefix recurrence and retirement capacity

Status: active, partial Lean results. No global rank invariant, terminal
purity theorem, or new sorting-depth coefficient is claimed. Work is in the
existing `tapered-945` worktree and is uncommitted/unpushed.

## What is implemented

`ClippedPrefix.lean` proves finite counting identities on the actual ordered
wire set of a source. For a threshold predicate, write `H` for its population,
`P(p)` for its population in the first `p` output positions, and
`d(p) = min(H,p) - P(p)`. Then:

```text
P(p) + d(p) = min(H,p)
count([p,q)) = min(H,q) - min(H,p) + d(p) - d(q).
```

The equalities with subtraction are in `Int`. Adjacent slots telescope
exactly. For the up-port, with `h=up/2` and source size `N`, the formula is

```text
count(up) = min(H,h) + H - min(H,N-h) - d(h) + d(N-h).
```

The two fringes are separate intervals. Neither can be replaced by a uniform
ancestor share. A native interval is the difference of two global thresholds;
the corresponding theorem retains all four signed endpoint deficits.

`wireKeyRank_threshold_iff` derives the relation between global key thresholds
and local key ranks. `wireThresholdDeficit_le_of_crossings` proves that two
rank-crossing bounds of size `E` give `d(p) <= E` for **every** threshold.
It selects the appropriate crossing direction, without charging `2E`.
The module also proves the clipped interval map is monotone/1-Lipschitz and
that an exactly sized sorted pool returns its ordered native cohorts.

`RaggedPrefixRoute.lean` proves source-key conservation for `raggedX`, then
the exact recurrence on the routed comparator execution. Its endpoint
`candidate_integer_prefix_recurrence` supplies one actual UB-23 port table
chosen **before** the network family, input permutation, receiver and key
threshold are quantified. The nominal term uses the input's actual threshold
population; the corrections use the same stage's actual output deficits.
This theorem includes bootstrap, roots, every frontier and meeting, with no
sorting premise. It is an exact recurrence, not a bounded-error induction.

`RaggedPrefixCohort.lean` proves threshold conservation across a physical
expansion cohort. Given the child register set equalities, its 64 child
threshold populations sum to the source population minus its up-port
population. Source-key conservation makes this an input/output execution
identity. `candidate_expansion_child_sets` derives the required physical set
equalities from UB-23's own source table, and
`candidate_expansion_threshold_cohort` instantiates the threshold identity on
the initialized schedule. `raggedWirePort_whole_up` proves contraction
preserves each whole child population. Composing the successive-stage
cohort identities into the six-stage bounded-error induction remains open.

## Retirement reveals a stronger count obligation

After an upper cut is permanently closed, every eventual native cleanup
component behind it must have its exact native cardinality. This follows
from ownership coverage, key bijectivity and disjointness of native regions;
`RetirementCapacity.pure_partition_exact_card` proves the general statement.

Suppose a retiring source has no up-port. Let `T_j` be the already stored
population in child subtree `j`, and let `B_j` be that subtree's native size.
Its outgoing block must satisfy

```text
D_j + T_j = B_j.
```

This is an exact integer condition, not a 69-wire discrepancy condition.
The existing `ScheduledEvenFlow` contract does not force it. A kernel-checked
example constructs two allowed top-advance splits at `C=2^40`, `e=0`,
source count `2^40`. Set

```text
E = 2^34 - 8668228,       M = 2^34 + 279620.
```

Both endpoint blocks have size `E`. The other blocks have size `M`, except
that eight middle blocks receive two extra wires. One allocation increments
indices `1..8`, and the other increments `2..9`. Both conserve the source
count, have even blocks, have up-port zero, and satisfy every current
`ScheduledEvenFlow` field. Their maximum block discrepancy is `26/15`, below
`evenFlowBlockError = 2 + 70/64`. Yet block 1 differs by two wires.
For any fixed `T_1`, both choices cannot satisfy the same exact native total.

`retirement_example_candidate_scale` locates `2^40` at the candidate's
`d=16`, `t=12` root top-advance. This identifies a genuine scale, **not** the
selected trace's actual count or chosen allocation. In particular, this is
**not a proof that `candidateIntegerSchedule` is unsortable**. It rules out
deducing retirement balance universally from the current local contract.
The particular choice still lacks a proof of the stronger property.

UB-23 remains complete for its stated count/ownership goal. UB-24 needs
either a stronger coordinated scheduler or a proof that its selected table
already satisfies exact component balance. The current independent local
choice does not expose such a property.

## Implemented rounding repair core

`CumulativeEvenRounding.lean` rounds a nonnegative ordered mass sequence via

```text
R(k) = 2 * floor((sum_{i<k} y_i)/2)
cell(i) = R(i+1) - R(i).
```

All cells are even, and their sums telescope. Every contiguous group has
rounding error **strictly below two wires**, regardless of the number of
registers in it. If its two cumulative boundaries are exact even integers,
the group's cardinality is exact. These facts are proved, including the
finite interval exactness theorem `roundedMassCell_interval_exact`.

The proposed next implementation is to order registers by a depth-first
tree traversal, so complete subtrees are contiguous, and apply these facts
to the shape-specific nominal register masses. Top components should have
exact native totals. Derive edge ports jointly from the subtree totals and
their parent/child boundary flows:

This is a construction plan, not a proved tree scheduler. For aggregate
subtree mass `T_b(t)`, routed conservation requires the coupled equations

```text
up_b(t)         = down_parent,b(t) - (T_b(t+1) - T_b(t)),
down_b,child(t) = T_child(t+1) - T_child(t) + up_child(t).
```

The parent-down and child-up terms cannot be omitted: subtree mass changes by
the incoming parent port minus the outgoing up-port. Required proofs:
depth-first subtree contiguity, nominal subtree mass identities, port
nonnegativity, evenness, conservation, vanishing/whole exceptional ports,
and the resulting rounding bounds. The new bounds need not be the old
one-wire up bound; recompute their charges in the rank budget instead of
silently reusing it.

## Aggregate audit: global conservation is not subtree anchoring

A read-only audit of the target formulas establishes a useful global identity:
the shape-specific target counts over all active bags sum to exactly `64^d`
(including bootstrap and meeting, where targets are native counts). For an
active-address prefix rooted at level `r`, however, the sum of target counts
in its active descendant bags is generally

```text
64^(d-r) - C_r/cap - (16/15) * e * C_r,
```

where `C_r` is the reference capacity at that prefix and `e` is its address
debt. Thus global conservation does not give native capacity at each proper
subtree. For example, at `d=14, t=2`, a bottom bag at level `r=2` with address
`x=1` has positive debt and a strict deficit from its native capacity. This
is a formula-level audit, not yet a Lean theorem about the selected integer
schedule.

The required laminar invariant must include the contribution retained by
ancestors (equivalently, the reserve represented by the `C_r/cap` and signed
debt terms). Applying cumulative rounding independently to raw target masses
of each subtree cannot supply that invariant. The existing
`SubtreeMass.complete_subtree_mass_eq` is a candidate algebraic ingredient,
but it does not yet identify actual stored ownership with the rounded masses.

The terminal meeting arithmetic is consistent:
`frontier_first_meeting_receive` combines the top parent's down port with the
64 bottom-cohort targets and equals the receiver's native reservoir. The
outstanding problem there is coordinated integer allocation and its rank
profile, not the nominal real-mass identity.

`retirement_complement_from_rounded_interval` now connects this rounding
bound to retirement: if a stored subtree is even, fits in its native
component, and has cumulative-rounded nominal mass, its exact native
complement is even and differs from the signed outgoing target by less than
two wires. This closes the local arithmetic while leaving the scheduler
obligations explicit.

`RetirementCumulativeSplit.lean` packages the per-child complements into an
existing `ScheduledEvenFlow .topAdvance`: if the complements sum to the
retiring source count, the split has zero up-port, even blocks, exact native
component totals, and block error below two (within the current `70/64 + 2`
allowance). The nominal complement identity is already available from
`top_advance_native_child_mass`; what is missing is the global invariant that
identifies each stored subtree with its rounded nominal interval and proves
exact source conservation at the retiring parent.

## Remaining acceptance gates

1. Prove an ancestor-reserve laminar invariant, then build one coordinated
   schedule from its subtree totals. The local complement lemma does not show
   that each retiring subtree's rounded mass is actually stored by
   `candidateIntegerSchedule`, and the coupled port equations still need
   nonnegativity, parity, and exact conservation proofs.
2. Prove the new static-debt bootstrap's native-prefix profile on those same
   ports, including pooled low/high fringes and source separator deficits.
3. Close a symbolic six-stage signed recurrence: cancel nominal ancestor
   and descendant terms before bounding approximation and rounding errors.
   Instantiate threshold-specific cohort history across contraction.
4. Prove upper retirement purity and all-order outsider preservation, then
   terminal parent-group localization for the revised cutoff. The older
   terminal file uses a different terminal level and needs adaptation.

UB-22 comparator realization and the final sorter/depth/asymptotic assembly
remain separate. The accepted bound is still 1419.

## Verification

On 2026-10-14 a fresh rebuild of all 38 local modules from this worktree
passed with Lean 4.29.0-rc4, including all nine endpoint axiom guards.
Every checked source hash matched the final source. The ticket validator
passed (19 tickets, with older unrelated stale-entry warnings), as did
whitespace/trust scans and both PowerShell checker syntax checks.

The focused entry point is `check-rank.ps1`. It rebuilds the local import
closure into a private directory and compiles `FrontierRankAxioms.lean`.
It reads existing best-package/Mathlib artifacts and does not download or
delete caches. Example from this worktree:

```powershell
& upper-bound/experiments/tapered/check-rank.ps1 `
  -LeanExe 'C:/Users/Varun/.elan/toolchains/leanprover--lean4---v4.29.0-rc4/bin/lean.exe' `
  -BestLib 'C:/Users/Varun/Documents/Projects/Math Research/sorting-network/upper-bound/best/.lake/build/lib/lean' `
  -BuildDir './LLM-helpers/ub24-fresh-build'
```

Nine endpoint guards permit exactly `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axioms, `native_decide`, or trust extensions are
introduced. No full package build or sorting-bound contribution check is
claimed by these partial results.
