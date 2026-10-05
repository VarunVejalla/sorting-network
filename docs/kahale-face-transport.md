# Discrepancy transport: exact law and a closure obstruction

## Status

The proved lower-bound coefficient remains `3.270559...` for base-two logs.
There is no new depth-rate inequality or improved coefficient in this update.

The context-dependent matrix update is now formalized in
`AKS/Kahale/FaceTransport.lean`, with guarded axiom checks in
`FaceTransportAxioms.lean`. Closure of the pair matrix alone for the
repository's ordered comparators remains open. An explicit counterexample
exists when comparator orientation is unrestricted.

## Checked transition law

Write `Q(i,j)` for the number of surviving faces with discrepancies at
`i,j`, and `C(i,j;b)` for those whose baseline input execution has a one
at wire `b`. For a gate with min output `a` and max output `b`, and a
third wire `j`, the exact update is

```text
Q'(a,j) = C(a,j;b) + C(b,j;a),
Q'(b,j) = Q(a,j) + Q(b,j) - Q'(a,j),
Q'(a,b) = 0.
```

Entries disjoint from the gate are unchanged. The module proves the min
formula, row balance, max formula, gate elimination, and untouched-entry
formula for any finite collection of signal states.

**Explicit hypothesis:** each relevant triple has distinct variable axes
and otherwise constants, or has no variable axes. This is the local shape
of a surviving or coalesced proper input face. The module does not yet
kernel-check preservation of the full proper-face shape from the original
input-set encoding. It also does not assert that `C` is a function of `Q`.

The local truth tables use `propext`. General results use subsets of the
usual `propext`, `Classical.choice`, and `Quot.sound` baseline. No new axiom
or trust extension was added.

## Stronger finite check for ordered comparator prefixes

`scripts/kahale_face_transport.py` compares equal-matrix reachable states
and computes **every** queried destination, even if it was absent from
the state catalogue. It also compares individual `C(i,j;b)` counts,
rather than only their sums in the transition formula.

| Wires | Reachable states examined | Equal-matrix state pairs examined | Different individual context or next matrix |
|---:|---:|---:|---|
| 5 | 43337, complete catalogue | 39231 | none |
| 6 | 175371, partial catalogue | 90718 | none |

The six-wire run uses a capped 100000-state BFS plus 10000 random walks
of length 40, seed zero. Pair comparisons use one representative per
matrix class; all queries on those comparisons are evaluated exactly.
These finite results do not prove general closure.

## Explicit obstruction when orientation is unrestricted

Use four wires numbered `0,1,2,3`. In the following prefixes, `(a,b)`
means **send min to `a` and max to `b`**, even when `a > b`:

```text
P = [(1,0), (1,2), (1,3), (3,2), (2,0)]
R = [(0,1), (0,2), (0,3), (3,2), (2,1)]
```

Their matrices agree at every base weight. The sole nonzero entry is

```text
Q^1(2,3) = 4.
```

But `C^1(2,3;0)` is four after `P` and zero after `R`. Appending the
same standard gate `(0,2)` gives

```text
after P: Q'^1(0,3) = 4,
after R: Q'^1(0,3) = 0.
```

This is an exact finite counterexample to matrix closure for unrestricted
orientations. It is also a counterexample for the relaxation consisting
only of monotonicity and weight preservation. These are actual directed
comparator executions, not arbitrary face contexts chosen independently.

**Scope:** both prefixes include gates excluded by Lean's `Comparator.h :
i < j`. They also violate prefix dominance: an ordered-comparator prefix
can only decrease the number of ones in each initial wire segment. Thus
this is not a counterexample to closure for the repository's networks.
The scripts and JSON record the exact input/output maps and the differing
coordinate; this counterexample has not been formalized in Lean.

As a separate relaxation check, exhaustive enumeration gives 297
monotone, weight-preserving, prefix-dominant four-wire maps, versus 261
reachable ordered-comparator states. Composing embedded maps from those
297 possibilities on five wires, a seed-zero 30000-step probe examined
2042 distinct relaxed states and found no transition counterexample.
The sampled relaxed maps are not asserted to be reachable by comparators.

## Consequence for the proof strategy

The pair matrix discards a genuine routing variable in the broader model:
occupation of a third wire in the same baseline execution. A closure proof
cannot follow from monotonicity, conservation, or face coalescence alone.
It must use stronger structure, such as ordered-comparator reachability.
The ordered finite evidence is worth pursuing, but does not justify
dropping the context from a proof.

### Why simply adding `C` does not settle closure

There is a further derived identity. If a gate `(a,b)` is disjoint from
the discrepancy pair `(i,j)`, that pair survives unchanged. Let
`H(i,j;a,b)` count these faces whose baseline has ones at both `a,b`.
Updating the baseline by AND/OR gives

```text
C'(i,j;a) = H(i,j;a,b),
C'(i,j;b) = C(i,j;a) + C(i,j;b) - H(i,j;a,b).
```

Thus singleton context updates naturally introduce two-wire occupation
correlations. Updating higher occupation moments can introduce still higher
ones. This identity does not prove nonclosure of `Q,C` on reachable states:
an additional realizability theorem might recover `H`. It identifies the
next proof obligation rather than assuming that keeping singleton contexts
solves the problem. The occupation-moment identities in this paragraph
are derived arguments, not Lean theorems in the new module.

The next substantive target is an inequality coupling `Q`, `C`, and
baseline occupations under ordered comparator layers. Initially we have
the derived constraints

```text
0 <= C(i,j;b) <= Q(i,j),
sum_(b outside {i,j}) C(i,j;b) = k * Q(i,j).
```

They need a further shared-execution compatibility constraint; treating
each entry as independently selectable repeats the earlier relaxation
problem. Any eventual lower bound must force a loss over a number of
layers proportional to `log_2 n`, rather than just require a terminal
repair. No such loss has been established here.

## Reproduction

```text
lake build AKS.Kahale.FaceTransport AKS.Kahale.FaceTransportAxioms
python -B scripts/kahale_face_transport.py --wires 5 --output docs/kahale-face-transport-five-results.json
python -B scripts/kahale_face_transport.py --wires 6 --limit 100000 --random-walks 10000 --output docs/kahale-face-transport-six-results.json
python -B scripts/kahale_face_relaxation.py --wires 5 --samples 30000 --output docs/kahale-face-relaxation-results.json
```

See [the coupled-face model](kahale-coupled-faces.md) for the sorting
criterion and [the method barrier](kahale-method-barrier.md) for why a
new compatibility constraint is necessary.
