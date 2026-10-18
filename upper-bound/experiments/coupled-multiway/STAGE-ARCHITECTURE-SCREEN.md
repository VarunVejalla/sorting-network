# Below-200 stage architecture screen

Status: cost and interface screen, not a construction. It evaluates the two
routes proposed in the current research notes: a direct high-arity stage and
parallel composition of smaller separators. The measured local AKS-style
contracts come from `upper-bound/experiments/ajtai-multiway/BELOW-200-PLAN.md`;
the composition barriers are recorded in that file and
`upper-bound/experiments/direct-multiway/RESEARCH-SEQUENCE.md`.

## Cost gate for a genuinely new recursive stage

If one complete stage reduces each recursively handled subproblem by factor
`p`, then all serial comparator layers in its partition, combine, repair, and
cleanup network must total `T_total < 200*log2(p)`. This is distinct from the
drop-in gate `T_node<400`, which keeps the old three-nodes-per-factor-64
schedule.

| Stage growth `p` | Growth bits | Strict total-depth budget for coefficient `<200` | Existing two-round core | Remaining budget for all combine/repair work |
|---:|---:|---:|---:|---:|
| 16 | 4 | `<800` | 72 layers at `(k,p)=(256,16)` | `<728` |
| 32 | 5 | `<1000` | 110 layers at `(k,p)=(1024,32)` | `<890` |
| 64 | 6 | `<1200` | no screened tuple in the current notes | — |
| 256 | 8 | `<1600` | no screened tuple in the current notes | — |

The 32-way row is the best concrete *depth-only* seed in the current
high-arity notes: it has five growth bits for 110 binary layers. It is not yet
a candidate sorter. The two-round core certifies an all-cut error around
`0.45`; the 16-way instance permits around `0.55`. For a middle cut, `0.45`
allows roughly `0.225N` wrong-side keys, or 7.2 nominal 32-way bin widths.
Nothing in that count bound localizes the errors or excludes a distant-bin
swap. The existing counterexample in `ajtai-multiway/BELOW-200-PLAN.md`
therefore blocks the proposed “repair adjacent boundaries, recurse on bins”
composition.

The remaining-depth budget is not the main issue. It is generous enough to
explore a sparse fixed repair for the 32-way core, but the repair must be
proved on the *reachable output profiles* of the exact two-round network and
must establish contraction of a rank-sensitive invariant. A generic
all-cut-count guarantee permits profiles for which local boundary repair
fails, regardless of whether its depth is 890 or 17.

## Parallel composition does not lower the price by itself

Running separators simultaneously on disjoint bags is already how the current
tree scheduler uses parallel depth. Their depths do not add across bags, but
the serial levels along a root-to-leaf path do add. A block of `m` successive
stages with growth factors `p_i` and depths `T_i` has coefficient
`sum(T_i)/sum(log2(p_i))`; regrouping those stages as a “macro-stage” changes
neither numerator nor denominator. Parallel composition helps only if it
creates a new joint network whose depth is below the sequential sum, while
preserving the stronger joint rank/cut contract. No current note gives such a
construction.

Thus the first route to test is the direct 32-way stage, not a relabeling of
several smaller stages as one. The 16-way tuple is a fallback if its stronger
error is useful enough to simplify the composition theorem; its smaller depth
budget and still-large `0.55` leakage make that uncertain.

## Most promising next theorem

Use the 32-way row-scramble core as a fixed candidate and seek a stronger
output contract with three parts:

1. a simultaneous bound, for every rank and cut, on the **number** of columns
   whose spill exceeds `w` wires (rather than only the total spill);
2. a bound on the distance of every nonexceptional wrong-side key from its
   target boundary, plus an explicit exception budget for long-range errors;
3. a one-stage rank-profile transfer inequality for the resulting 32 child
   regions, including fresh error, so the coupled local/global recurrence
   contracts and implies exact terminal purity.

The current universal adversary forces at least 15 exceptional columns at
one-bin spill for the 1024-column instance, and at least 7 at two-bin spill.
So “no bad columns” cannot be the target; the sensible first screen is a
sharp `O(p)` tail bound, followed by a fixed repair demonstrably within the
890-layer margin. The lower-bound construction is summarized in the
row-scramble plan and should be used as a sanity check for any tail theorem.

If that tail theorem cannot be established from the actual fixed scrambles,
the current AKS certificate is not enough to justify further network search.
The next fallback is to recover the omitted finite-parameter AKPS p-way
combination argument or its cited k-sorting writeup. The reported private
60–100 binary coefficients are not usable parameter data, and the published
1992 paper does not give the combine operation or an end-to-end recurrence.

## Decision

**Go** on one bounded analysis: derive the 32-way reachable spill-tail and
localized-crossing profile for the existing fixed two-round core. **No-go** on
formalizing the generic halver theorem further, searching arbitrary 17-layer
repair networks, or building a full recursive sorter before this interface
survives. The cost arithmetic is favorable; composability is the decisive
unknown.

This route is more promising for below 200 than the tapered Chvatal family,
whose best ideal screen is already 528, but it has substantially greater
proof risk. It has not yet shown that its `O(p)` tail target is true for the
fixed construction, nor that a tail bound of this form suffices for the
coupled recurrence.
