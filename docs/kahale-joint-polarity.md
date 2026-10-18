# Shared minimum/maximum logic and mixed witnesses

## Status

This follows [residual image difficulty](kahale-image-difficulty.md).
The new results are exact finite Python screens and derived all-size
transport identities. There is no new Lean theorem or improved universal
coefficient; the checked lower bound remains 3.270559454.

The missing information is now explicit: pairwise inversion witnesses
can come from different inputs, whereas AND/OR at a comparator needs
coexistence in one input. For a full parallel layer, an output-pair
decision can require a joint four-coordinate witness. This supplies a
precise constraint for a future structural inequality, not yet the
inequality establishing an asymptotic penalty.

## 1. A sound finite screen retaining comparator polarity

For image `R`, record which pairs `a<b` can be inverted: some `x in R`
has `x_a=1,x_b=0`. A stronger signature records this separately at each
input weight `k`. Zero inversions characterize sorting exactly.

The script `kahale_joint_polarity.py` uses the complete image graphs
through five wires. It identifies equal signatures and adds a signature
edge whenever an actual parallel comparator layer gives that transition
on some representative image. Reverse BFS gives quotient completion
distances, which are lower bounds on actual completion distances: every
actual suffix projects to a quotient path. A quotient path may switch
hidden representative images between layers, so it can be spuriously
short. This is an existential relaxation, not a claimed deterministic
update law.

| Wires | Images | Unweighted classes | Rankwise classes | Rankwise exact distances |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 2 | 2 | 2 | 2/2 |
| 3 | 7 | 7 | 7 | 7/7 |
| 4 | 44 | 40 | 44 | 44/44 |
| 5 | 581 | 357 | 567 | 579/581 |

The unweighted screen gives exact distances on 476/581 five-wire images.
Both five-wire screens give initial lower bound five, compared with
the weaker dependency-cone relaxation. This is a finite result derived
using actual image transitions, not a scalable depth theorem. The
rankwise signature nearly identifies the entire small image catalogue;
its accuracy alone is not evidence of asymptotic compression.

We intentionally retain inversion predicates rather than every pair
projection. Full pair projections conditioned on weight would determine
every image point through five wires: each weight has at most two ones
or at most two zeros, which identify that point. That would make a small
pairwise success largely tautological.

## 2. An actual counterexample to rankwise pair closure

Consider the two five-wire prefixes

```text
A: [(3,4)], [(0,1),(2,3)], [(0,2)]
B: [(1,3),(2,4)], [(1,2)], [(0,1)].
```

Their inversion signatures agree at every weight. Nevertheless appending
the same gate `(3,4)` gives different signatures.

At weight two, image A contains mask `6`, with ones at wires 1 and 2:
wire 1 is one while **both** wires 3 and 4 are zero. Image B has no
weight-two point with wire 1 one and wires 3 and 4 both zero. It has
separate inversion witnesses: mask `10` witnesses `(1,4)`, and mask `18`
witnesses `(1,3)`. Those witnesses cannot be combined into one input.

After `(3,4)`, output 4 is the OR of inputs 3 and 4. The inversion
`(1,4)` at weight two therefore persists for A and disappears for B.
The saved result includes the complete images and their shared signature.
This is an ordered, realizable-prefix counterexample; it does not rely
on reversed gates or an arbitrary unattainable domain.

The five-wire catalogue also contains equal rankwise signatures with
different actual completion depths, two versus three. Thus a single
deterministic residual-difficulty value cannot be recovered from this
signature in general.

## 3. The exact shared-witness state

For disjoint coordinate sets `A,B`, define

```text
W_k(A;B) = exists x in R with |x|=k,
           every coordinate in A one, every coordinate in B zero.
```

The same `x` must satisfy every requested bit. Pair inversions are the
case `|A|=|B|=1`; the hidden counterexample is
`W_2({1};{3,4})`.

For one gate on `a<b`, with outputs `u=min(a,b)` and `v=max(a,b)`, and
a distinct coordinate `c`, the exact directed-pair rules are

```text
W'_k({u};{c}) = W_k({a,b};{c})
W'_k({c};{u}) = W_k({c};{a}) OR W_k({c};{b})
W'_k({v};{c}) = W_k({a};{c}) OR W_k({b};{c})
W'_k({c};{v}) = W_k({c};{a,b}).
W'_k({u};{v}) = false.
```

These are substitutions of AND/OR, with weight unchanged because the
gate conserves the number of ones. They explain exactly where separate
pair witnesses cease to suffice.

### Parallel gates require four-coordinate coexistence

For two disjoint gates `(a,b)` and `(c,d)`, requesting that the first
minimum be one and the second maximum be zero requires

```text
W'_k({min(a,b)};{max(c,d)}) = W_k({a,b};{c,d}).
```

All four conditions must hold on one image point. Independent tests of
the two gates, or their marginal pair witnesses, cannot replace this.

For an arbitrary parallel layer, substitute the following clauses for
each requested output bit:

| Requested bit | Input clauses |
| :--- | :--- |
| minimum = 1 | both gate inputs = 1 |
| minimum = 0 | at least one gate input = 0 |
| maximum = 1 | at least one gate input = 1 |
| maximum = 0 | both gate inputs = 0 |

Expand the conjunction into mixed input patterns, discard contradictions,
and take the OR of their witness predicates. If both outputs of one gate
are constrained, enforce both jointly. In particular output pattern `01`
has exactly input possibilities `01` or `10`; `00` and `11` have only
their identical input patterns. This keeps the conservative paired gate
semantics that dependency cones omit.

An output pattern on at most `r` coordinates pulls back to input patterns
on at most `2r` coordinates. Hence one step of pair transport can be
computed from order-four mixed witnesses. This is an exact transport
between orders, **not closure at a fixed order**. Repeated substitution
can grow arity exponentially with depth; the research problem is to
extract a quantitative inequality without retaining the whole image.

These formulas use existential witnesses. A counting version must avoid
double-counting overlapping OR clauses; the local `00/01/10/11` partition
gives a disjoint expansion. Counting clauses independently would be wrong.

## 4. Checks and what is still missing

On five wires, the script checks 58,100 single-gate output-pair transports
and 145,250 full parallel-layer transports against directly simulated
images. Those include 14,525 four-coordinate-pattern queries. Smaller
complete catalogues also pass. Both output values are substituted from
the same gate and witnesses come from the same image point.

This provides a concrete next object: mixed witness families across
rank cuts, with shared-gate transport. To improve the lower-bound
coefficient we still need to prove that some necessary loss accumulates
across scales. A finite signature quotient, or a longer exact expansion
of Boolean functions, does not supply that loss. The repeated efficient
growth prefixes and mirror/median families remain necessary challenges.

The next screen should test candidate charges based on **compatible
four-coordinate witnesses across gates and neighboring ranks**, checking
whether a layer can resolve obligations concurrently or merely transfer
them to another pattern. First demonstrate a nontrivial charge on the
exact completion benchmark, then test replicated and nested prefixes;
only after a valid general inequality should it enter Lean.

A technical warning for this work: propagating an overapproximate image
and finding that it cannot sort does not prove the actual image cannot
sort. Ghost inputs can create a false obstruction. A lower-bound
relaxation must admit every actual comparator schedule, as the existential
quotient used here does. Incomplete sampled transition graphs are also
insufficient to certify a quotient distance lower bound.

## Reproduction

```text
python -B lower-bound/experiments/scripts/kahale_joint_polarity.py --output docs/kahale-joint-polarity-results.json
```

Standard-library Python only. The saved file records quotient bounds,
actual closure counterexamples, mixed hidden witnesses, and transport
check counts. No Lean changes, builds, axioms, or dependencies were added.
