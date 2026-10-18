# Sparse concentration and exact pool selection: next-target audit

Status (2026-10-10): informal constructions and numerical cost exploration.
Existing entropy-halver and known-half-partition theorems are kernel checked
in the legacy package. Their new adapters, uniform numerical bounds, and the
complete replacement root repair are not proved here.

Follow-up: the [uniform envelope and suffix audit](uniform-bound-and-suffix.md)
now supplies exact rational entropy ceilings and a conditional **444**-layer
uniform first-split budget. The 406 candidate below is not a uniform bound.
The remaining three levels do not follow from half purity alone.

## 1. A much weaker concentration primitive is sufficient

The recursive concentration argument only needs a halver capturing one
extreme cohort into **half** the outputs. It does not need a 1/32 fringe,
both directions at once, large-cohort routing, or fixed accuracy 1/199.
The existing restricted-halver theorem already provides a sufficient family;
constructing a new expander is not necessary for this first candidate.

For a block of `m` wires with at most `K` wrong-half keys, choose side size
`b=m/2` and supported fraction `alpha=K/b=2K/m`. Choose an error `epsilon`
less than 1/2. The half-halver captures all but `floor(epsilon*K)` wrong keys
into the appropriate half. Recurse with budgets `K` and
`floor(epsilon*K)`, in parallel, as in the preceding concentration note.

The existing [entropy family](../../alternatives/legacy/AKS/Separator/PatersonFamily.lean)
gives depth at most the natural-number ceiling of

    h(alpha,epsilon) = 1 +
      [H(epsilon*alpha) + H((1-epsilon)*alpha)] /
      [-epsilon*alpha*log((1-epsilon)*alpha)],

where `H` is binary entropy using natural logarithms. At sparse support,

    lim_{alpha -> 0} h(alpha,epsilon) = 1 + 1/epsilon.

This follows from `H(x)=x log(1/x)+x+O(x^2)`; it is an informal asymptotic
calculation, not a new Lean theorem. For `epsilon=1/4`, illustrative depths
are ceilings 6 at `alpha=1e-4`, 7 at `.02`, and 8 at `.2`. The full 989-depth
separator was paying for very different guarantees.

Stop and include a whole block in the repair pool when `K > sigma*m` for
a chosen density `sigma`. This keeps `alpha <= 2*sigma <= 1` at every
nonterminal call. Sparse descendants use cheaper support-dependent depths.
Higher error reduces primitive depth but increases the total fixed core:
both children must remain active when the complement's leakage budget is
nonzero. That branching cost matters.

### Singleton optimization

When `K=1`, use an ordinary balanced max/min comparison tournament. Its
fixed winner wire contains the wrong key if one exists. Its depth is
`ceil(log_2 m)` and its core has one wire. This avoids repeatedly paying
the entropy-halver ceiling to capture a single extreme key.

### Odd-size adapter still needed

The halver theorem takes `2*b` inputs. An odd-size recursive block needs
one virtual pure extreme key, followed by a restriction adapter. A largest-key
concentrator pads with a smallest key; a smallest-key concentrator pads with
a largest key. The real dirty block has `ceil(m/2)` wires and the complement
has `floor(m/2)` wires. The wrong-key cohort does not gain a member.

This needs an explicit comparator-network proof, especially for the
smallest-key padding/reindexing convention. The numerical recurrence assumes
it; it is not supplied by the scalar experiment. Alternatively, maintain
even arities by rounding blocks and audit that extra core/depth cost.

## 2. The final layout needs one layer, not 33

Once pool repair succeeds, the native-half label of every upper wire is a
fixed function of its position. The number of high keys in the target lower
half equals the number of low keys in the target upper half. Match those
misplaced positions once and compare each matched pair; low goes left,
high goes right. The comparisons are disjoint and their endpoints have the
correct index order, so this has depth one.

The existing [known-half partition](../../alternatives/legacy/AKS/Sort/KnownHalfPartition.lean)
proves exactly this mechanism for a representative permutation. Extending it
to a fixed binary label pattern uses the same matching or threshold
commutation. `|U|` is even, so no power-of-two padding is needed here.
The remaining adapter proof is small and does not require the full
known-permutation correction.

This improves the previous sufficient layout estimate from 33 to 1.
It does **not** sort within either half or deliver the other bin guarantees.

## 3. Numerical candidate for the first split

Run `python upper-bound/experiments/paterson/sparse_halver_budget.py`.
The script uses exact rational leakage floors and floating-point entropy
ceilings. It uses the maximal root-window size budgets, not a uniform
envelope over every admissible placement/size.

A candidate with `epsilon=1/4`, stopping density `sigma=1/10`, gives:

| Quantity | Candidate budget |
|---|---:|
| Longest concentration path | 152 layers |
| Core per level-2 bag | 585,781 wires |
| Core per level-4 bag | 6,122 wires |
| Total pool including root/cold | 3,048,013 wires |
| Complete bitonic pool sort | 253 layers |
| Final native-half layout | 1 layer |
| First split total | **406 layers** |

This is a significant reduction relative to the preceding 6144-layer
concentration baseline, and is below the old 561-layer *complete* root
repair. But it is not yet a replacement: the old repair supplies all needed
bin guarantees, whereas this candidate supplies only exact native halves.
The remaining three partition levels have a budget of at most 155 if the
complete new repair is to beat 561. They may cost more.

Formal obligations before using even the 406 number are: logarithm/entropy
certificates for every selected integer depth, the odd-size adapter, a uniform
size bound, the recursive fixed-core proof, exact pool-count/selection proof,
and the binary-layout adapter. A floating-point ceiling must never become a
Lean depth hypothesis without certification.

## 4. Can the pool be partitioned more cheaply than sorting?

The pool needs an **exact fixed-cut selection** network: its smallest `a`
keys must occupy one fixed output set, where `a` is determined by counts of
already-pure outside wires. It does not need their internal order.

However, `a` need not be half the pool size, and the actual keys in the pool
need not have an input-independent binary label pattern. The one-layer known
half matching therefore applies only *after* selection, not to the pool
itself. A positive-error halver does not establish this exact selection.

There is also a large unconstrained component: the root and cold storage
can contribute roughly 607,000 wires. Their first-split labels are not
specified by the stranger invariant. Cheap sparse correction alone does not
remove that selection problem. The precise number of their low/high keys
depends on the rest of the admissible state.

Three candidate implementations are worth distinguishing:

1. **Complete pool sort.** Already available and robust for any cut; this
   supplies the 253-layer candidate above. It is the baseline to beat.
2. **Truncated bitonic selection.** For an exact power-of-two median, sorting
   two halves in opposite directions and doing the first merge layer costs
   `h(h-1)/2+1`, rather than `h(h+1)/2`. For `h=22`, that saves 21 layers.
   Arbitrary pool cuts and sizes do not inherit this saving without a new
   construction. This is a modest opportunity, not a route to tens of layers.
3. **Structured pool selection.** Maintain sorted runs or separate known
   low/high fringes so an exact merging/selection network can exploit them.
   The current recursive cores are arbitrary value sets, not sorted runs.
   Sorting those runs first also has a depth charge. No advantageous exact
   merge budget has been established here.

Simply choosing a small halver epsilon is expensive: to force zero leakage
for a possible cohort of `K` keys requires `epsilon*K<1`. In the existing
entropy formula the sparse-support depth then grows on the order of `K`.
Recursive concentration avoids this cost for sparse bag contaminants, but
does not make the unconstrained pool disappear.

## 5. A useful lower constraint on concentration

If a network of depth `d` must capture a possible unique maximum from any of
`m` positions into a fixed core of `F` outputs, then

    F * 2^d >= m.

Each output depends on at most `2^d` input wires. If some input lies outside
the union of core dependencies, placing the unique maximum there contradicts
capture. Thus `d >= log_2(m/F)`. This is an elementary informal dependency
argument; the repository already has relevant dependency machinery.
It explains why shrinking the core and minimizing depth compete, but it
does not rule out the numerical candidate or a much better one.

## Decision and next obligation

The sparse-support route is concrete enough to justify a modular concentration
lemma using the existing entropy family. It does not yet justify replacing the
production root sorter. For a practical improvement, first obtain uniform
certified bounds for the sparse concentrator and determine whether the other
three bin levels fit the remaining repair budget. For an ambitious repair
cost below 200, the pool selection step and its unconstrained component need
a substantially better argument; changing the concentration constants alone
is insufficient with the current full-sort baseline.
