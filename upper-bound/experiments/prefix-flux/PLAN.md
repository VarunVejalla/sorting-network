# UB-42: signed prefix flux and exact small frontiers

2026-10-20. Codex (GPT-6). Conjectural global-proof search for coefficient
at most300. No new separator, sorting algorithm or Lean theorem claimed.

## Use the existing exact identities

UB-24 already proves the Boolean threshold recurrence: if a bag has H zeros,
and Y(p) is its output zero count before port cut p, then

    Y(p) = min(H,p) - d(p),
    count([p,q)) = min(H,q)-min(H,p)+d(p)-d(q).

The up-port consists of two end intervals, not one uniform share. Reuse these
identities; the new task is a bounded invariant on the actual global flow.
The existing Chvatal proof estimates errors independently. Their opposite
signs may permit a stronger joint prefix analysis, but cancellation alone
does not imply a small per-bag error or exact final sorting.

## Fully specified threshold-contract test

Use `slackfree/explicit.py:build_table` with its existing integer D2 flow
table, initially (x,y,z)=(2,3,2). A state records each occupied bag's wire
capacity a and threshold zero count H. Initially all N=k^d wires are at the
root with a chosen global threshold q. At an active node, the fixed ports
are low up-fringe, k child blocks, high up-fringe. The Boolean oracle chooses
integer cumulative zero counts Y_j at their endpoints p_j, subject to:

- Y_0=0, Y_last=H; every port has between0 and its size many zeros.
- max(0,H-(a-p_j),min(H,p_j)-E) <=Y_j<=min(H,p_j), E=floor(epsB*a/2).
- h=up/2, Jmax=floor(deltaF*h). For j=min(H,Jmax)>0, at least
  j-ceil(epsF*j)+1 zeros lie in the low fringe; the symmetric constraint
  captures the largest min(a-H,Jmax) ones in the high fringe.
- Nodes with a<=C use exact prefix counts Y_j=min(H,p_j).

Whole-bag upward routing needs no comparison. Route port counts through the
actual table, conserving zeros and wires. A local LP can maximize next-step
misplaced colors relative to native rank intervals. This greedy policy is
only one adversary: a passing run is not a proof or worst-case upper bound.

At termination, every bag must have exactly

    min(R,max(0,q-address*R))

zeros, where R=k^(d-level) is its native interval size. Exact final local
sorts then suffice. Any nonzero discrepancy is a failure of this contract
and oracle policy, regardless of a small aggregate error fraction.

## Realizability and scope of a negative trace

Sorting the Boolean values inside each port realizes the chosen endpoint
counts with all intermediate prefix deficits bounded by the maximum endpoint
deficit. Assign local ranks increasingly among zero positions and among one
positions. For every local-rank cut p, its rank-crossing count equals the
Boolean deficit min(H,p)-Y(p). Thus this stable two-color permutation realizes
the all-cut rank bound as well. The two fringe bounds at min(H,Jmax) and
min(a-H,Jmax) imply the all-supported-rank fringe promises under this stable
assignment. Fresh-context review confirmed these endpoint implications for
epsF>0 and 0<=deltaF<=1.

This is only a relaxation of the local postconditions. Ascending comparators
also preserve or increase each input prefix's zero count and fix sorted
inputs. The count-only oracle forgets the input order, so it may violate those
additional constraints even on a single input. A negative trace therefore
refutes a proof from these postconditions and conservation alone; it does not
refute the full comparator-network contract or a particular implementation.

## Cost hypothesis, not a candidate bound

For (2,3,2), the unchanged flow uses5/4 stages per binary log. If every
ordinary stage had depth<=240, the leading coefficient would be<=300. The
nominal top-capacity window suggests exact sorting of a small upper band
could fit this budget; its cardinality and all exceptional cases must be
derived before making a cost claim. Large roots during the early clipped
top phase are not small frontiers and cannot be sorted exactly for free.

The prototype may initially use an exact root for a finite diagnostic.
That is explicitly unpriced: a successful all-n proof needs an actual
constant-depth root provider with its own nonzero error allowance.

First test a finite grid of epsB, epsF, C and thresholds. A negative exact
trace is useful evidence; a positive trace only motivates the next invariant
derivation. No Lean until a primitive, uniform induction, terminal purity,
complete depth budget and fresh-context review all close.
