# Coupled Boolean faces and discrepancy-pair coalescence

## Status and purpose

The proved base-two lower-bound coefficient remains `3.270559...`.
This investigation develops an exact coupled-execution requirement that
retains input identities and their shared comparator decisions. It supplies
a concrete object for a new structural argument, not a new asymptotic bound.
The depth-rate lemma is still missing.

Checked Lean results: a six-signal model of four executions, exact single-axis
routing, discrepancy contraction, irreversible coalescence, one-collision
accounting for a proper face, and a sufficient full sorting criterion.
All focused builds and guarded axiom audits passed. The local finite truth
tables use only `propext`; the general proofs use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Four executions share one network

Choose an input one-set `S` and distinct positions `p,q` outside it. Execute
the same network on

```text
00: S,
10: S union {p},
01: S union {q},
11: S union {p,q}.
```

At each wire, restricting its monotone Boolean function to this face gives
one of six signals: `0`, `1`, `x`, `y`, `x AND y`, or `x OR y`.
These signals are closed under a comparator's pointwise min/max operations.
`CoupledFaces.execFace_eval` proves that executing the signal model agrees
exactly with all four ordinary Boolean executions.

Initially there is one `x` signal, one `y` signal, and otherwise constants.
As long as the middle runs remain different, this pattern persists:

- comparing an axis with `0` routes it to the max output;
- comparing an axis with `1` routes it to the min output;
- comparing the two distinct axes changes them to AND and OR.

Once the middle runs agree, they stay equal under every continuation. An
AND/OR signal cannot recreate a variable axis. Thus the two discrepancies
coalesce exactly when a comparator brings them together, at most once.

`face_axis_balance` checks the local contraction identity;
`applyFace_axis_balance` and `execFace_axis_balance` prove

```text
final axis count + 2 * opposite-axis comparisons = initial axis count.
```

For a proper two-axis face, `proper_face_collision_bound` bounds the count
by one and `proper_face_coalesced_iff_collision` characterizes elimination
by that single collision. `execFace_middle_equal_iff` connects zero axis
signals to equality of the two actual middle executions. The global theorems
take the initial count-two condition explicitly rather than defining a
particular initial-set encoding in this module.

## Why every face must coalesce

The middle inputs have the same Hamming weight, so a sorting network must
give them the same output. Conversely, if every such pair agrees, exchanging
one member at a time connects all input sets of the same cardinality. The
network therefore has one output per input weight. A sorted input of that
weight is fixed by every standard comparator, so that output is sorted.

`FaceSortingCriterion.exchange_constant_of_equal_card` kernel-checks this
connectivity argument. `sorts_of_coalesces_all_faces` proves the sufficient
direction, including full sorting through the 0–1 principle. It also covers
arity zero and one. The necessary direction uses the ordinary uniqueness
of a sorted Boolean vector of a fixed weight; it is explained here, not an
additional iff theorem in this module.

This requirement is exact. It is stronger than finding a separate admissible
route for each discrepancy while ignoring the common input on which the
routes depend.

## A discrepancy-pair matrix

For each base weight `k`, let `Q_t^k(i,j)` count proper input faces whose
middle runs still differ at the pair of wires `i,j` after prefix `t`.
Every surviving face is counted once. Initially

```text
Q_0^k(i,j) = binom(n-2,k),
total faces at weight k = binom(n,2)*binom(n-2,k).
```

A comparator `(a,b)` eliminates exactly `Q_t^k(a,b)` faces. For a disjoint
parallel layer `L`, all these counts refer to the same pre-layer state:

```text
survivors_(t+1) = survivors_t - sum_((a,b) in L) Q_t^k(a,b).
```

After a complete sorting network every matrix is zero. This matrix-level
counting identity is derived; the current Lean module formalizes the exact
per-face contraction and sequential accounting underlying it.

### The routing context that cannot be freely chosen

For distinct `a,j,b`, let `C_t^k(a,j;b)` count faces at pair `(a,j)` whose
baseline `00` execution has a one at wire `b`. A comparator `(a,b)` gives

```text
Q'_(a,j) = C(a,j;b) + C(b,j;a),
Q'_(b,j) = Q(a,j)+Q(b,j)-Q'_(a,j),
Q'_(a,b) = 0.
```

Entries with both endpoints outside the gate stay unchanged. The baseline
has exactly `k` ones, and both discrepancy positions have baseline zero, so

```text
0 <= C(a,j;b) <= Q(a,j),
sum_(b outside {a,j}) C(a,j;b) = k * Q(a,j).
```

These are exact derived identities. The contexts come from the same Boolean
executions for all pairs and all weights. Treating each queried `C` as an
independently selectable number would be a further relaxation whose strength
has not been established. The numerical matrix alone may or may not determine
the needed sums on general reachable states.

This is the concrete new quantitative target: bound the rate of eliminating
pair mass using **realizable, shared routing contexts**, and connect that rate
to the certificate-growth relaxation. Raw conservation alone is insufficient.

## Finite evidence on the Fibonacci barrier schedules

At each depth we sampled 1024 faces at each of three base weights near
`n/4`, `n/2`, and `3n/4`, with seed zero. For middle-weight faces:

| Depth | Wires | Surviving fraction | After two adjacent repair layers |
|---:|---:|---:|---:|
| 32 | 36 | 0.2607 | 0.1123 |
| 40 | 161 | 0.6289 | 0.5205 |
| 48 | 738 | 0.8623 | 0.8320 |
| 56 | 3459 | 0.9580 | 0.9521 |
| 64 | 16530 | 0.9932 | 0.9932 |

Every sampled transition obeys the exact coalescence rule. These fractions
are samples, not population estimates with a claimed confidence level, and
they do not prove a limiting rate. Finite `d/log_2(n)` also differs materially
from the limiting Fibonacci coefficient.

The eight-wire odd-even transposition sorting control enumerates all 1792
proper faces across all base weights. Every face coalesces. This is an exact
finite computation, not a new formal verification of that sorting network.

### Exact fixed-face witnesses beyond a missing adjacent comparison

Orient every comparator edge from its smaller index to its larger index and
take the union DAG across the unpatched barrier schedule. For incomparable
vertices `p,q`, set `S` to the union of their strict successor sets. The sets
`S`, `S+p`, `S+q`, and `S+p+q` are all upward closed in that DAG. Hence all
four runs are fixed by every comparator of the original schedule.

The script constructs and verifies such faces exactly. Examples:

| Wires | Axes | Separation |
|---:|---:|---:|
| 161 | 78,99 | 21 |
| 738 | 549,639 | 90 |
| 3459 | 1546,2114 | 568 |
| 16530 | 6732,10031 | 3299 |

An adjacent parallel repair layer moves either discrepancy by at most one
wire. Eliminating a pair at initial separation `r` thus requires at least
`ceil(r/2)` such layers. All recorded faces still survive the two appended
odd/even layers, even though those layers include every adjacent comparator.

These are exact finite family witnesses, with base sets encoded in the JSON.
The DAG construction and repair bound are derived arguments, not Lean
theorems. The repair bound is **only for adjacent-comparator repairs**: an
arbitrary comparator could merge one selected pair immediately. No universal
obstruction to every Fibonacci-rate schedule follows from these examples.

## Matrix transition consistency: encouraging, not yet a theorem

The second probe enumerates actual Boolean wire-function states and groups
them by all their `Q^k` matrices. It asks whether two states with the same
signature can have different next matrices under the same comparator.

| Wires | States examined | Scope | Inconsistent next update found |
|---:|---:|---|---|
| 5 | 43337 | complete reachable catalogue | no |
| 6 | 175371 | capped BFS plus 10000 length-40 random walks | no |
| 7 | 81316 | capped BFS plus 5000 length-40 random walks | no |

For five wires there are 4106 matrix signatures. For six and seven wires
the catalogues are partial; transitions whose destination is missing are
excluded. The random seed is zero. All profile counts are exact integers.

Some equal-matrix states on five and six wires are not related by any input
permutation, as verified by exhausting those permutations for the recorded
pair. Thus the observed consistency is not solely input-label symmetry.
Nonetheless, it does not prove a general closed transition law. A larger
counterexample remains possible. Even an exact closed law would need a
nontrivial depth-rate inequality to improve the coefficient.

## Next mathematical work

1. Establish a general transition law for the matrix, or produce a genuine
   nonclosure witness and identify the missing shared context.
2. Find a scale-independent inequality linking realizable pair transport to
   simultaneous certificate growth. Challenge it on arbitrary reachable
   states, not only this one bad schedule.
3. Prove a rate loss across a number of layers proportional to `log n`, with
   controlled endpoint costs. A few extra terminal layers do not suffice.

The promising change of direction is the exact sorting requirement and its
input-dependent routing compatibility. There is not yet evidence sufficient
to forecast an improved coefficient, particularly one above 4.

## Reproduction

```text
lake build AKS.Kahale.CoupledFaces AKS.Kahale.CoupledFacesAxioms AKS.Kahale.FaceSortingCriterion AKS.Kahale.FaceSortingCriterionAxioms
python -B scripts/kahale_coupled_faces.py --depths 32 40 48 56 64 --samples 1024 --output docs/kahale-coupled-faces-results.json
python -B scripts/kahale_face_matrix.py --wires 5 --output docs/kahale-face-matrix-results.json
python -B scripts/kahale_face_matrix.py --wires 6 --limit 100000 --random-walks 10000 --output docs/kahale-face-matrix-six-results.json
python -B scripts/kahale_face_matrix.py --wires 7 --limit 10000 --random-walks 5000 --output docs/kahale-face-matrix-seven-results.json
```

This follows the reassessment of the
[hierarchy-layer barriers](kahale-hierarchy-layer.md) and the original
[scalar method barrier](kahale-method-barrier.md).
