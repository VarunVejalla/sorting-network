# A layer constraint from joint occupations, and its limitation

## Result

We obtain a genuine coalescence budget from the Johnson-graph spectral gap,
and an exact layer update using actual joint wire occupations. However,
the simplest proposed connection to inefficient certificate growth fails
on actual ordered comparator prefixes. No improved lower-bound coefficient
follows. The proved coefficient remains `3.270559...` for base-two logs.

The useful new distinction is between **an available collision reserve**
and **a reserve that costs inefficient certificate growth to create or spend**.
The latter has not been proved, and it is false as a universal local claim.

## 1. Use actual executions on one weight slice

Fix middle-input weight `w`, with `1 <= w < n`, and let `N = binom(n,w)`.
For each input of this weight, execute the prefix. Write

```text
m_i = number of these inputs having a one on output wire i,
G = sum_i m_i * (N - m_i),
R = number of still-distinct neighboring middle-input pairs,
E = 2*N*R - n*G.
```

Here `R` is the total of the discrepancy-pair matrix with base weight
`k = w-1`. Each neighboring input pair is counted once. `G/N^2` is the
sum of occupation variances under the uniform weight-w distribution.

For a gate `(a,b)`, define actual counts on this same slice:

```text
A = number of inputs with gate values (1,0),
B = number of inputs with gate values (0,1),
T = number of inputs with gate values (1,1).
```

The old one-counts are `A+T` and `B+T`; the new counts are `T` and
`A+B+T`. Expanding their variances gives

```text
G_before - G_after = 2*A*B.
```

There is no independence assumption here. `A` and `B` count joint gate
patterns in actual executions; their product is just the expression in
this identity.

For a disjoint layer, put `P = sum_gates A_g*B_g` and
`K = sum_(a,b in layer) Q(a,b)`. The pair contraction and occupation
polarization identities give

```text
R_after = R_before - K,
G_after = G_before - 2*P,
E_after = E_before - 2*N*K + 2*n*P.
```

## 2. The global realizability constraint

The inputs of weight `w` form the Johnson graph `J(n,w)`. Its degree is
`w(n-w)` and its first positive Laplacian eigenvalue is `n`. The adjacency
eigenvalues are given in [Suzuki's lecture notes, Lemma 7.1](https://icu-hsuzuki.github.io/t-algebra/lec7.html);
subtracting them from the degree gives Laplacian eigenvalues
`r(n+1-r)`. These spectral facts are external mathematical results, not
kernel-checked in this update.

For each Boolean output function `f_i`, the spectral gap bounds its
edge boundary below by `n` times its unnormalized variance. Every
surviving middle-input edge differs on exactly two output wires, so
summing boundaries over wires counts it twice. Therefore

```text
2*N*R >= n*G,  i.e. E >= 0.
```

Combining this constraint at the next state with the exact update gives
the layer inequality

```text
2*N*K <= E_before + 2*n*P.
```

Unlike freely selectable pair contexts, the quantities in this inequality
come from the same actual input distribution. Initially

```text
R_0 = N*w*(n-w)/2,
G_0 = N^2*w*(n-w)/n,
E_0 = 0.
```

After sorting, `R=G=E=0`. Hence the total variance-drop budget has fixed
endpoints, and the reserve must eventually be discharged. Neither this
fact nor the inequality supplies a layer-count penalty on its own.

## 3. A counterexample to charging reserve spending to height loss

Consider the three-layer four-wire sorter

```text
L1 = [(0,1), (2,3)]
L2 = [(0,2), (1,3)]
L3 = [(1,2)]
```

Every comparator has equal input scalar heights under the existing update
`(a,b) -> (min(a,b), max(a,b)+1)`. Starting at zero, its heights are

```text
after L1: [0,1,0,1]
after L2: [0,1,1,2]
after L3: [0,1,2,2].
```

On the weight-two slice (`N=6`), the exact ledger is:

| Layer | Killed faces `K` | Products `P` | Reserve before | Reserve after |
|---|---:|---:|---:|---:|
| L1 | 4 | 8 | 0 | 16 |
| L2 | 0 | 2 | 16 | 32 |
| L3 | 8 | 8 | 32 | 0 |

Thus the final layer spends the entire reserve and completes sorting,
with no unequal-height comparator. A universally positive local charge
from reserve spending to scalar height inefficiency is false. A global
asymptotic statement with endpoint or scale-dependent terms is not ruled out.

The network's full sorting property and equality of heights at every
comparator are kernel-checked in `OccupationCounterexample.lean`. The
integer reserve profile above is an exact Python computation.

## 4. One cheap layer creates a leading-order reserve

This is also an obstruction at arbitrary size, not just a small example.
For even `n`, compare any perfect matching of initial wires. On the
central slice `w=n/2`, every gate has

```text
A = B = binom(n-2,w-1).
```

All input heights are zero, so the layer is fully efficient. Its reserve is

```text
E_1 = n*A*(n*A - N).
```

Relative to the full initial collision cost `2*N*R_0`, this is

```text
E_1 / (2*N*R_0)
  = w*(n-w)/(n-1)^2 - 1/(n-1)
  = (n-2)^2 / (4*(n-1)^2) -> 1/4.
```

Thus a scalar reserve can store a leading-order amount after just one
efficient layer. It cannot be treated as a negligible endpoint allowance.
This family is a derived counting argument; the JSON records exact rational
evaluations at `n=4,8,...,512`.

## 5. Exact finite challenge

`scripts/kahale_layer_occupation.py` enumerates actual reachable Boolean
wire-function states, and queries every nonempty disjoint layer and every
nontrivial weight slice. All queried destinations are computed directly.

| Wires | Reachable states (complete) | Layer/slice queries | Reserve-spending queries | Spending with all gate heights equal |
|---:|---:|---:|---:|---:|
| 4 | 261 | 7047 | 375 | 117 |
| 5 | 43337 | 4333700 | 390470 | 71124 |

All integer contraction, polarization, and reserve identities passed;
all computed reserves were nonnegative. Heights are those of the recorded
BFS representative prefix, not an invariant of the Boolean-function state.
These counts are descriptive, not an asymptotic frequency estimate.

The first spending witness on four wires is the prefix `[(0,1),(0,2)]`
followed by `(1,2)`: on weight two, `K=2`, `P=2`, and `E` falls from
eight to zero, with equal comparator heights.

## 6. What is actually formalized

`AKS/Kahale/OccupationLayer.lean` proves:

- population decompositions for actual finite Boolean signals;
- the exact comparator occupation-variance drop;
- its sum over a family of gate input pairs;
- the reserve update from the explicit contraction and variance hypotheses;
- the coalescence inequality **conditional on spectral nonnegativity**.

The disjoint-layer interpretation of the pair sum and the Johnson-graph
spectral constraint are derived here; they are not yet an end-to-end Lean
theorem for arbitrary comparator layers. No spectral assumption was added
as an axiom. The conditional theorem takes it as a hypothesis.

`OccupationCounterexample.lean` checks the actual four-wire sorter and its
scalar-height efficiency. Guarded audits for both modules use only subsets
of `propext`, `Classical.choice`, and `Quot.sound`. No new trust extension
was introduced.

## 7. Next target

Do not claim a depth improvement from this scalar reserve or invest in a
large spectral formalization before finding a rate consequence. It shows
where coalescence can be funded, but loses how that funding is distributed
among input sets and certificate scales.

A more discriminating candidate should retain the distribution of reserve
across spectral degrees, jointly with certificate information. The reserve
is a weighted sum of higher-degree occupation components: the degree-one
part cancels because its Laplacian eigenvalue is `n`. The initial matching
can create degree-two components cheaply; a useful lemma would constrain
how mass reaches and leaves degrees growing with `n`, while certificates
also grow. Neither such a constraint nor an improvement above `3.270559...`
has been established. The concrete next challenge is whether equal-height
layers can also recycle this degree-resolved reserve without a sustained
loss; this should be tested before another proof scaffold is built.

## Reproduction

```text
lake build AKS.Kahale.OccupationLayer AKS.Kahale.OccupationLayerAxioms AKS.Kahale.OccupationCounterexample AKS.Kahale.OccupationCounterexampleAxioms
python -B scripts/kahale_layer_occupation.py --wires 4 --output docs/kahale-layer-occupation-four-results.json
python -B scripts/kahale_layer_occupation.py --wires 5 --output docs/kahale-layer-occupation-five-results.json
```

Background: [context-dependent face transport](kahale-face-transport.md)
and [the original scalar method barrier](kahale-method-barrier.md).
