# Repair interfaces: extraction works, staged amplification is obstructed

Research review: 2026-10-07. Logarithms are base two. This follows
[the initial amplification investigation](sorter-amplification.md).
The asymptotic limit of D(n)/log n is not proved here. No sorting-depth
coefficient has improved.

## Status map

Kernel checked in focused standalone Lean runs:

- `AKS/Sort/RepairInterface.lean`: removing s parallel layers from an
  arbitrary sorter gives rank displacement strictly below 2^s. Threshold
  outputs are exact outside a corresponding narrow band.
- `AKS/Sort/Dependency.lean`: binary graph ancestors have cardinality at
  most 2^depth. Restricted-state single-coordinate pivotal witnesses and
  disjoint change sets impose matching lower bounds on repair fan-in.
- `AKS/Sort/RepairBarrier.lean`: an input support and an attainable-rank
  cover at the last wire obey n+1 <= |A|+|R|. Concrete binary input and
  suffix cones instantiate this. Variable-arity product arithmetic is
  checked conditional on its cut inequalities.
- `AKS/Bounds/ConditionalLimit.lean`: a uniform additive defect in
  dyadic depth composition implies a dyadic ratio limit, by Fekete's lemma.
  The defect hypothesis is explicitly an argument, not a proved result.
- `AKS/Bounds/DyadicLimit.lean`: minimum depth is monotone; a dyadic
  ratio limit implies the full base-two logarithmic ratio limit. Together
  these give a full conditional convergence criterion.

Derived mathematical argument, not a complete formalization of macro modules:

- The cut theorem and standard cone bookkeeping imply an obstruction for
  staged m-wire modules plus binary repair layers. This includes partial
  modules made of ordinary comparators, not only exact sorting gates.
- The geometric two-partition repair construction is described below,
  but its entire executable network and depth bound are not formalized.

Exact finite computation:

- The reachable-state probe exhausts all Boolean inputs for each selected
  8-input base prefix and 16-input matching lift. Its conclusions concern
  those specific networks, not optimal repair networks or all lifts.

## Universal extraction is stronger than we initially assumed

Write a sorter as P followed by s parallel layers. An item at output
wire i of P can finish in at most 2^s positions. Those positions cover
every rank attainable at i. Attainable ranks form an interval (the Knuth
lemma used by Kahale et al.), and sorted inputs leave wire i unchanged.
Consequently every rank at i differs from i by less than 2^s.

The repository already formalized the rank-cover and displacement bridge;
`RepairInterface` exposes it directly as an interface. No deletion of
inactive gates is needed for this argument. Taking s=o(log m) gives a
rank radius m^o(1) for the truncated m-sorter. Thus extraction of a local
interface from an arbitrary sorter is possible at this scale.

Related published structural results on the final layers:
[Codish, Cruz-Filipe, and Schneider-Kamp, Sorting Networks: the End Game](https://arxiv.org/html/1411.6408).
The formal proof here uses the existing rank-interval route rather than
claiming that all tail interaction components have bounded size.

## Repair and its necessary dependence on ambiguity

For a Boolean array that is sorted outside a single interval of width w,
sort blocks of length 2w in two staggered partitions. The interval is
contained in a block of one partition. Ascending comparators preserve
its sorted exterior, so that partition finishes sorting. The depth is
at most 2D(2w), with edge blocks treated by restriction or padding.
Unknown interval location does not by itself prevent O(log w) repair.
For general ordered inputs this argument works threshold by threshold,
if every thresholded array satisfies the width-w promise.

Two staggered partitions also appear in Section 4.4 of
[Towards Simpler Sorting Networks and Monotone Circuits for Majority](https://kozmath.github.io/papers/upper_bounds.pdf).

This dependence on w cannot disappear for a generic interval promise:
take an all-one interval and the w inputs with one zero at each possible
position. Exact sorting forces the first output to distinguish all of
them from the all-one baseline. Its ancestor cone must contain w inputs,
so repair depth is at least ceil(log w).

Geometric locality is sufficient, not necessary. Fixed distant partners
can repair many errors in one matching. The more general test considers
the actual reachable-state family C: if changing coordinate i alone can
change the required output bit on C, i must be in that repair output's
cone. Disjoint chunks that each admit such a change also require distinct
ancestors. These two tests are kernel checked in `Dependency`.

**Qualification to our previous discussion:** that sufficient-but-not-necessary
statement concerns arbitrary restricted families C. If C is the full image
of a comparator-network prefix on unrestricted original inputs, and the
repair finishes global sorting in s layers, `rankLocal_of_sorts` already
forces displacement below 2^s. In this setting cheap final repair necessarily
requires geometric rank locality. Distant prescribed partners are not a way
around that necessity. They may still help intermediate partial tasks.

The concrete cut theorem also gives the kernel-checked inequality

    N+1 <= 2^(prefix depth) + 2^(repair depth).

Hence a depth-d lift of one fixed base sorter on N=mb inputs cannot be
finished with uniformly small exact repair as b grows: repair depth is at
least log(N+1-2^d) when the quantity inside the logarithm is positive.
For fixed d this is asymptotically log N. A hierarchy using many lifted
stages and only a final exact repair is not excluded by this single-cut
observation; its entire prefix has growing depth.

## A stronger obstruction: variable-arity staged composition

Suppose a proposed construction consists of parallel stages of local
modules. A module touches at most m wires and is a comparator network
on those wires. Binary correction stages may be interspersed. Each stage
has a maximum module arity k_i (binary stages have k_i=2).

Let

    P_j = product of k_i before cut j,
    Q_j = product of k_i after cut j,
    T = product of all k_i = P_j Q_j.

The input cone of any wire at the cut has size at most P_j. Its possible
destination set has size at most Q_j. The kernel-checked cut theorem
therefore implies, for every cut,

    N+1 <= P_j+Q_j.

### Why the cut theorem holds

Consider the last wire of the prefix, an input support A, and a cover R
of every attainable rank at that wire. Put zeros on A and ones outside
A. The prefix output at the last wire is zero, because it agrees there
with the all-zero input on its support. Sorting this Boolean input by a
rank permutation and commuting the monotone threshold through the prefix
shows that a rank below |A| is attainable there. Rank N-1 is also
attainable there: sorted inputs remain unchanged. The interval lemma
then forces at least N-|A|+1 attainable ranks into R. Hence

    N+1 <= |A|+|R|.

A correct sorting suffix supplies R via possible destinations of that
wire's value. This argument applies to arbitrary local comparator
modules; it never assumes a module fully sorts its own inputs.

The published access proof gives the related uniform-arity obstruction:
[Dobrokhotova-Maikova, Kozachinskiy, and Podolskii, Constant-Depth Sorting Networks, Theorem 4](https://drops.dagstuhl.de/storage/00lipics/lipics-vol251-itcs2023/LIPIcs.ITCS.2023.43/LIPIcs.ITCS.2023.43.pdf).
The variable-arity conclusion here is derived using our cut formulation.
No novelty claim is made.

### Consequence for the amplification budget

Choose the cut just before P first reaches N/2. Since the crossing
stage has arity at most m, its previous prefix product is at least
N/(2m); the cut inequality forces Q>N/2. Thus

    T >= N^2/(4m),
    sum_i log k_i >= 2 log N-log m-2.

The integer product version is kernel checked in `layer_product_barrier`,
conditional on the cut inequalities. The module-cone bookkeeping and
logarithmic interpretation are mathematical deductions, not additional
Lean theorems in this change.

If there are L stages of m-wire modules and B binary stages, this yields

    L log m+B >= 2 log N-log m-2.

In particular, for N=m^r and L=r,

    B >= (r-1)log m-2.

Therefore adding o(log m) binary repair depth per scale cannot make this
staged construction sort. A startup allowance depending on m cannot fix
the deficit as r grows. Allowing each module to be a truncated sorter
does not evade the obstruction. If stage expansion is instead
m/2^sqrt(log m), the required repair is still asymptotically log m per
stage. That proposed near-unit-loss budget is obstructed as well.

The arithmetic statement excluding B=r*e+B0 with 2^e<m and any fixed
startup B0 is separately formalized as `no_uniform_small_repair`.

This is stronger than the earlier observation that exact opaque gates
alone require roughly twice as many stages: cheap binary corrections
also cannot restore coefficient-preserving amplification here.

### Exact scope

The obstruction concerns a sequence of complete parallel local-module
stages plus binary correction stages. A module of arity m means that
each output depends on at most those m input wires and each value stays
inside that module during the stage.

Matching lifts can interact with far more than m wires over their d
internal binary layers, despite having only m base wire types. They are
not m-arity modules and are not excluded by this theorem. Pipelining
overlapping unfinished modules also needs a separate analysis: if it
cannot be grouped into the asserted stages, this accounting does not
apply. The limit-existence question itself remains unresolved here.

## Finite closure probes

Run `python scripts/sorter_repair_interface_probe.py` (NumPy required).
The script emits every single-coordinate pivotal witness for the central
sorted bit on the exact image of each prefix.

| Base/lift | Omitted base layers | Reachable states | Uncertain width | Pivotal coordinates | Repair depth lower bound |
| --- | --- | --- | --- | --- | --- |
| 8 inputs | 0 | 9 | 0 | 1 | 0 |
| 8 inputs | 1 | 12 | 2 | 2 | 1 |
| 8 inputs | 2 | 15 | 4 | 4 | 2 |
| 8 inputs | 3 | 23 | 6 | 6 | 3 |
| Identity lift, 16 inputs | 0 | 81 | 16 | 16 | 4 |
| Seed-0 matching lift, 16 inputs | 0 | 163 | 12 | 14 | 4 |
| Seed-0 matching lift, 16 inputs | 1 | 278 | 12 | 16 | 4 |

The sampled lifted prefixes with one omitted layer, seeds 0 through 3,
all have 16 pivotal coordinates. This is a necessary lower bound on
standalone exact repair; it does not prove that four repair layers suffice.
The interaction structure preserved by the original tail is not preserved
automatically by these lifts. Conversely, failure of these small lifts
does not establish asymptotic impossibility for all lifts.

### Bounded suffix synthesis

`scripts/sorter_repair_search.py` encodes a fixed-depth binary suffix on
the entire exact prefix image in Z3. Matching constraints are explicit;
all states are checked simultaneously by bit-vector operations. Tail
comparators are restricted to span at most 2^(remaining layers+1)-1,
using `Kahale.active_comparator_width_le`. An equivalent suffix can
remove inactive comparisons, so this restriction loses no valid sorting
completion. A SAT model is rechecked by ordinary Boolean execution on
every reachable state. UNSAT results have not been independently certified
or formalized and must be treated as solver evidence.

For the 5-layer lifted prefixes, a 4-layer repair was UNSAT for the
identity lift and seeds 0 and 1 (144, 278, and 296 reachable states).
Thus the pivotal-coordinate test is not sufficient in these instances.
Reproduce with `--identity`, `--seed 0`, or `--seed 1` and
`--tail-depth 4 --timeout-ms 60000`.

At repair depth 5, the identity and seed-0 searches both timed out after
60 seconds. These UNKNOWN results do not imply either existence or
nonexistence. No repair construction was obtained from this search.

## Other approaches assessed

- **Exact packet comparison:** a valid universal interface, but each
  compare-split requires logarithmic depth in packet length. It does not
  fit the target budget.
- **Bounded relative uncertainty with periodic repair:** even if its
  recurrence is stabilized, a remaining constant fraction of N inputs
  costs order log N to sort by a fresh generic network. The final bill
  has to be accounted for explicitly.
- **Small geometric buffers after every module stage:** extraction is
  available on the original sorter, but uniform staged closure would
  contradict the product obstruction at the desired budget.
- **Prescribed correction partners:** more expressive than geometric
  buffers for arbitrary restricted families and intermediate tasks, but
  not an escape from locality for exact final repair of a full prefix
  image. They cannot evade the staged product obstruction on their own.
- **Internal-layer mixing or genuine pipelining:** survives the current
  obstruction. No uniform repair/closure theorem or coefficient estimate
  has been obtained. This is a substantially harder structural problem.
- **Bounded-defect multiplicative composition:** would give a limit via
  Fekete and dyadic squeezing; the full implication is now checked. It
  remains a conditional criterion, not a construction of that composition.

## Recommendation

Stop searching for a universally composable interface made of completed
m-wire module stages with tiny added repairs: the target budget is
incompatible with the cut obstruction. If we continue amplification,
the next claim must explicitly describe internal interactions across
module boundaries and avoid this architecture. A useful target is a
pipeline invariant whose ambiguity cones remain controlled while parent
comparisons begin before child work finishes. We currently have no
reason to assert that an arbitrary near-optimal sorter supplies one.

## Verification limits

The new Lean files were checked using the installed pinned
`v4.29.0-rc4` compiler directly against cached project and dependency
oleans. The normal `lake` entry point first tried a network download;
invoking installed Lake directly then failed while inspecting the local
Mathlib Git checkout. Neither dependencies nor toolchains were updated.
This is a focused source check, not a full clean repository rebuild.
Concurrent Chvatal files were not edited.
`AKS/Bounds/AmplificationAxioms.lean` guards the main theorem dependencies;
the checked results use only `propext`, `Classical.choice`, and `Quot.sound`.
