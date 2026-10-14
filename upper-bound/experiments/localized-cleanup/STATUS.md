# UB-26 status

Resumed by Codex (GPT-6), 2026-10-14. Branch/worktree:
`ub-26-localization` / `.claude/worktrees/ub-26`.

The existing Chvatal early-stop route remains screened out: its optimistic
recursive cleanup cost exceeds 1419, and its outsider invariant does not imply
positional locality. This resumed pass investigates a cheaper composition
lemma for any future physical s-sorted prefix. Previous good screen commit:
`c718d42`; parking commit: `09194dc`.

Claim level: `hand-proof` for the conditional cleanup recurrences below;
`model` for the source-based depth screen; no new sorting theorem.

## Done

- Read the current Chvatal assembly and confirmed that the repeated prefix
  ends in rank-pure blocks of `2^42` wires (`RealBlocks.lean`). The existing
  final stage sorts these blocks in parallel at depth at most 903.
- Derived two recursive composition targets: rank-pure blocks need one
  recursive cleanup; an arbitrary s-sorted interval needs two overlapping
  cleanup passes.
- Improved the s-sorted cleanup: recursively sort aligned chunks of length
  `2B` once, then merge only the disjoint `B`-by-`B` seams using Batcher's
  odd-even merge network. The conditional recurrence is
  `F(n) <= P(n) + max_{k<4B} F(k) + log2(2B) + O(1)`, giving coefficient
  `(p+theta)/(1-theta)` and gate `p < 200-201*theta` (149.75 at theta=1/4).
- Exhaustively checked the Boolean chunk/seam cleanup with a fixed odd-even
  merge comparator generator: 139,506 s-sorted inputs through n=16, and all
  equal-run Boolean count pairs through run length 16. This is simulation,
  not a theorem.
- Screened early stopping of the existing Chvatal prefix. The checked proof
  establishes rank purity only at fixed `2^42`-wire blocks. Its fractional
  outsider invariant does not directly give purity or a contiguous
  s-sorted interval at larger block sizes.
- Traced the invariant through `Tree.lean`, `ExecPlacement.lean`, and
  `WireFlow.lean`: outsider counts constrain key ranks within logical bags,
  while physical supports are recursively assembled rank slices of earlier
  wire sets. No order/interval property of those supports is part of the
  invariant. Even exact bag purity plus arbitrary interleaving of bag supports
  permits a Boolean output with a dirty interval of length `N`; sparse
  outsiders can also be spatially dispersed. Therefore the invariant alone
  cannot yield the required physical localization contract.
- A rough stranger-tail screen suggests suppressing all errors around an
  `N^theta` native rank block may leave an unresolved rank region as large
  as `N^(1.186*theta)`. This is a model calculation, not a localization
  theorem, and it omits physical wire-set geometry.
- Under the optimistic assumption that this rank region is a physical dirty
  interval, two-pass recursive cleanup prices the stopped Chvatal prefix at
  `1419*(1-theta)/(1-2*1.186*theta)`, which is worse than 1419 for every
  positive theta. So this particular early-stop route is screened out.
- The exact schedule-specific interval-component geometry remains unbounded;
  it would require a separate analysis of `wireSets`, since `blockOf` selects
  consecutive *ranks within a set*, not necessarily a physical interval.
- Identified rank-pure partitioning as the primary construction target for
  this ticket. It has the easier depth gate `p<200*(1-theta)`.

## Not done

- No binary prefix with coefficient below that gate is known.
- The odd-even merge proof, all-n cleanup lemma, and recursive depth estimate
  have not been formalized.
- No Lean source, executable network, or sorting-bound theorem has been added.

## Next step

The current early-stop Chvatal route remains a poor investment: the optimistic
rank-width recurrence is already worse than 1419, and its invariant cannot
establish physical localization. Continue UB-26 by finding a new prefix for
the now-cheaper seam-cleanup interface. The next useful step is to formalize
the odd-even merge and the all-n cleanup lemma, then screen candidate prefixes
against the `p < 200-201*theta` gate. Exact Chvatal `wireSets` component
analysis is lower priority unless it enables such a candidate.

## Verification

`python scripts/tickets` passed on the branch after the claim update. The
checked source was inspected but not rebuilt. The recurrence algebra is
conditional hand analysis, not kernel-checked.
