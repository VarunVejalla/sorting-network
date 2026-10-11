# Joint routing groups and conditional certificate obligations

## Status

This investigation supplies a derived structural certificate inequality,
exact adjacent-weight and graph update laws, and finite simultaneous
concentration challenges. It does **not** improve the proved coefficient
`3.270559...`, and no Lean formalization was attempted.

The main inequality is

```text
conditional zero-certificate size >= pivotal-group size + meet-graph cover number.
```

Small exhaustive searches exhibit a cost for completing neighboring weight
slices together. That is evidence for investigating joint constraints,
not evidence of a sustained asymptotic penalty or coefficient above four.

## 1. Exact shared-baseline model

For a baseline one-set `S`, write `v(S)` for the output of a prefix.
Every missing input position `p` produces one additional output one in
`v(S+p)`. Let `A_i(S)` be the positions whose additional one goes to wire
`i`, and `r_i(S)=|A_i(S)|`. These sets partition the missing positions.
They are empty at occupied output wires.

For a gate `(a,b)`, the group update depends on the two baseline bits:

| Baseline bits | New min group | New max group |
|---|---|---|
| 00 | empty | `A_a union A_b` |
| 01 | `A_a` | empty |
| 10 | `A_b` | empty |
| 11 | empty | empty |

The union is disjoint. This update retains the actual baseline rather than
treating routing contexts as independently chosen.

### Square consistency couples adjacent weights

For missing `p,q`, let the routes from `S` be `a,b`, and the routes from
`S+p` and `S+q` to the common upper input `S+p+q` be `c,d`.
Conservation gives

```text
e_a + e_c = e_b + e_d.
```

If `a != b`, the upper labels must be `c=b,d=a`. If `a=b`, the upper
labels must agree at a different wire, `c=d!=a`: an output already made
one by the first addition cannot receive the second additional one.
This is stronger than choosing a separate routing partition at each weight.

Define, per wire and base weight `k`,

```text
U_k(i) = sum_(|S|=k) r_i(S),
B_k(i) = sum_(|S|=k) r_i(S)^2,
T_k(i) = number of faces whose lower additions share one wire,
         and whose upper addition appears at wire i.
```

Counting the upper additions in the squares gives the exact law

```text
(k+1)*U_(k+1)(i) = (n-k)*U_k(i) - B_k(i) + 2*T_k(i).
```

Here `B` measures concentration, while `T` records the second-order
activation it produces elsewhere. Summing over wires collapses to a
tautological mass identity; the wire labels and certificate obligations
must be retained to obtain a stronger bound.

## 2. A structural inequality using conditional certificates

Fix a zero-valued output wire `i` at `S`. A zero certificate valid at
this baseline is a subset `C` of its missing input positions such that
setting the positions in `C` to zero forces output `i` to zero.

Every such certificate contains `A_i(S)`: adding a pivotal position would
otherwise preserve all its zeros while making the output one. Conversely,
the intersection of all these certificates is exactly `A_i(S)`.

On the remaining missing positions define the **meet graph** `G_i(S)`.
The edge `{p,q}` is present when neither single addition makes output `i`
one, but their joint addition does. Every zero certificate valid at `S`
must meet this edge, for the same extremal-input reason. As its endpoints
are outside the pivotal group, the obligations are disjoint. Therefore

```text
c_i(S) >= r_i(S) + tau(G_i(S)),
```

where `c_i(S)` is the minimum valid zero-certificate size and `tau` is the
minimum vertex-cover size. This is an elementary derived argument, not an
asserted published improvement or a kernel-checked theorem.

This bound uses the **same baseline** for the certificate and the routing
group. It passes the earlier OR/AND example where a wire of scalar height
zero has a very large routing group.

### Exact graph update

When both baseline gate bits are zero, put `A=A_a(S)`, `B=A_b(S)` and
write `G_a[B]` for edges of `G_a` contained in `B`. Then

```text
G'_min = complete_bipartite(A,B) union G_a[B] union G_b[A],
G'_max = (G_a union G_b) restricted outside A union B.
```

The complete bipartite part comes from two additions routed to opposite
gate endpoints. The internal parts come from a lower join at one endpoint
and an upper meet at the other. Other second-order activations pass to the
max output, unless absorbed into its expanded pivotal group.

For baseline bits 01 or 10, the min inherits the zero-valued input's graph;
the max graph is empty. For 11, both graphs are empty. Thus the core and
meet-graph state has an exact comparator update, not an arbitrary new
context term.

In the 00 case, the complete bipartite edges force

```text
tau(G'_min) >= min(|A|,|B|).
```

More precisely,

```text
tau(G'_min) = min(|A| + tau(G_a[B]), |B| + tau(G_b[A])).
```

A cover of the complete bipartite part must contain all of at least one
side. This formula accounts for the inherited internal obligations too.
It does not imply that the conditional certificate size increases by this
amount: an existing certificate can already pay it. That amortization
problem remains open.

## 3. Feasibility evidence

The routing-group probe enumerates the complete reachable ordered-comparator
catalogues, independently computes certificate cores and minimum sizes by
enumerating zero certificates, and verifies square consistency, the moment
law, the certificate inequality, and the graph update.

| Wires | Reachable states | Input-square checks | Baseline/gate graph updates | Conditional zero-certificate checks |
|---:|---:|---:|---:|---:|
| 4 | 261 | 6264 | 25056 | 8352 |
| 5 | 43337 | 3466960 | 13867840 | 3466960 |

The certificate bound was tight in 2837172 five-wire queries and strict in
629788. These are counts over states and baselines, not independent samples
or an asymptotic frequency estimate. All checks passed.

### Fastest simultaneous concentration

Breadth-first search using **disjoint layers**, rather than comparator count,
finds the following minimum completion depths. A completed weight slice
has all its routing groups coalesced; its output is sorted because the
sorted input of that weight is fixed by the ordered network.

| Wires | Single slices | Adjacent slices | Minimum depth |
|---:|---|---|---:|
| 4 | any of 1,2,3 | one alone | 2 |
| 4 | — | 1+2 or 2+3 | 3 |
| 5 | any of 1,2,3,4 | one alone | 3 |
| 5 | — | 1+2 or 3+4 | 4 |
| 5 | — | 2+3 | 5 |

For five wires, the largest achievable minimum coalesced-face fraction
over weights 2 and 3 is

| Depth at most | Best minimum fraction |
|---:|---:|
| 0 | 0 |
| 1 | `1/5` |
| 2 | `7/15` |
| 3 | `3/5` |
| 4 | `4/5` |
| 5 | 1 |

Thus independently finishing either weight in three layers does not give
a common three-layer network, even approximately at the completion endpoint.
These are exact finite exhaustive computations, not Lean proofs.

An additional Z3 feasibility model uses one shared layer schedule across
all target inputs, with no unproved symmetry restriction. SAT witnesses are
independently executed. For six wires it reports:

- Weight 3: depth two UNSAT; depth three SAT.
- Weights 2 and 3: depths two through four UNSAT; depth five SAT.

For seven wires, weight 3 is UNSAT at depth three and SAT at depth four.
The joint weights 3 and 4 are UNSAT at depth three, but depths four through
six timed out after five seconds each. Those UNKNOWN results are
**inconclusive**, not impossibility results. SMT UNSAT reports are not
kernel-checked proof certificates. No large-width conclusion is inferred.

## 4. Why the pair graph alone is insufficient

Consider the simple baseline potential `sum_i(r_i+tau(G_i))`. Initially it
is `z`, where `z=n-|S|`. After sorting, the final zero outputs are thresholds
on the `z` missing inputs. Only the last zero output has singleton
activations, giving pivotal mass `z`. Only the penultimate zero output has
pair activations, giving a complete graph on `z` vertices and cover size
`z-1`. Earlier zero outputs need at least three additions to activate.

Consequently the final potential is `2z-1` for `z>=1`, rather than the
full conditional certificate sum `z(z+1)/2`. Its endpoint ratio is below
two. The same limitation holds for any nonnegative baseline weighting of
this unweighted wire sum. An exponential-growth argument for this scalar
potential cannot provide a leading logarithmic coefficient.

This is not a barrier for every graph-based or position-weighted invariant.
It identifies why simply summing the new inequality is inadequate.

## 5. Next mathematical target

Retain activation hypergraphs at **growing orders**, together with their
shared-baseline incidence across neighboring weights. For order cutoff `L`,
the final sorted certificate lower bound sees the last `min(L,z)` zero
outputs and sums to

```text
sum_(j=0 to min(L,z)-1) (z-j).
```

Fixed `L` has only constant endpoint amplification. Orders growing with
`n` are needed if this kind of potential is to yield a logarithmic rate;
for this unweighted growth-bound argument, `log L` must itself be of order
`log n` (for example, `L=n^alpha` with fixed positive `alpha`).
The meet graph is the order-two base case, with an exact update and an
explicit forced-cover charge. Higher activations require hitting sets,
and their shared gate update must account for obligations being transferred
or absorbed rather than assuming every creation is new work.

The next concrete challenge is an amortized inequality for these growing
orders that survives the mirror/median prefixes and the repeated four-wire
certificate-growth gadget. No such inequality is proved here, and no
numerical improvement is forecast from the finite completion gaps alone.

## Reproduction

Run from the repository root:

```text
python -B lower-bound/experiments/scripts/kahale_joint_groups.py --wires 4 --output docs/kahale-joint-groups-four-results.json
python -B lower-bound/experiments/scripts/kahale_joint_groups.py --wires 5 --output docs/kahale-joint-groups-five-results.json
python -B lower-bound/experiments/scripts/kahale_joint_slice_sat.py --wires 6 --depths 2 3 4 5 --output docs/kahale-joint-slice-six-results.json
python -B lower-bound/experiments/scripts/kahale_joint_slice_sat.py --wires 7 --depths 3 4 5 6 --output docs/kahale-joint-slice-seven-results.json
```

The SMT probe uses the locally installed Z3 4.13.4. Solver timings and
witness choices can vary; the saved results identify each outcome and
timeout. No new Lean files, axioms, or package dependencies were added.

Background: [degree recycling](kahale-degree-recycling.md),
[certificate families](kahale-certificate-families.md), and
[the scalar method barrier](kahale-method-barrier.md).
