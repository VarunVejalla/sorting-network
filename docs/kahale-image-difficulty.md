# Residual image difficulty: exact benchmark and a joint obstruction

## Status and outcome

This continues [the preparation investigation](kahale-certificate-preparation.md).
The universal kernel-checked coefficient remains 3.270559454. Everything
new here is a derived argument or exact finite Python computation, not
a Lean theorem or an asymptotic improvement.

We now have a complete small-image benchmark, a precise necessary joint
dependency model, and an explicit obstruction that individual support
sizes miss. We also know two limitations: cube and information costs
cannot simply be added, and dependency reachability alone has an
asymptotic ceiling of one logarithmic coefficient on powers of two.
The remaining structural target must retain the shared Boolean functions
implemented by comparators, as well as where information can travel.

## 1. The exact residual problem

For a prefix `P`, let `R=im(P)` on Boolean inputs. Define `H(R)` to be
the minimum number of parallel comparator layers that sort every member
of `R`. A suffix only needs the image; it does not need to know which
original input produced a particular image point.

Every reachable image contains the `n+1` already sorted Boolean inputs,
because ordered comparators fix them. An image is fully sorted exactly
when it consists of these inputs. Applying a layer to an image is exact:
apply that layer to every image point and take the resulting set.

`kahale_image_difficulty.py` closes the full Boolean cube under all
nonempty ascending matchings. It computes shortest prefix paths by BFS,
then exact completion distances by reverse BFS from the sorted image.
No wire symmetry is assumed, and every recorded optimal suffix is
independently simulated on every image point.

| Wires | Reachable images | Exact full sorting depth |
| ---: | ---: | ---: |
| 2 | 2 | 1 |
| 3 | 7 | 3 |
| 4 | 44 | 3 |
| 5 | 581 | 5 |

All catalogues completed. The minimum completion depth among images
reachable with prefix budget `t` is just `max(D(n)-t,0)`; that frontier
is a consistency check, not a new tradeoff theorem. The useful data are
the different remaining difficulties of individual images.

## 2. Required rank decisions and a coupled dependency relaxation

The sorted output at position `n-k-1` is the Boolean decision
`T_k(x)=1[|x|>k]`. A set of image coordinates `U` determines this
decision if no two image points agreeing on `U` have different values
of `T_k`. Let `s_k(R)` be its minimum size. If a suffix has depth `r`,
every output's syntactic dependency cone has at most `2^r` coordinates,
so `r >= ceil(log_2 max_k s_k(R))`.

A particularly transparent mandatory coordinate set is

```text
E_k(R) = { i : some x in R has |x|=k, x_i=0, and x+e_i in R }.
```

Every coordinate in `E_k` must influence output `n-k-1`. These singleton
differences cannot be resolved using other coordinates. The number of
different rank outputs requiring a fixed coordinate also gives a forward
fan-out bound: one signal can reach at most `2^r` outputs in `r` layers.

The joint model keeps a cone `C_j` at every physical wire. Initially
`C_j={j}`. A comparator on `a,b` updates **both** cones to `C_a union C_b`;
other cones stay unchanged. A final cone assignment must simultaneously
satisfy `E_k(R) subset C_(n-k-1)` for every rank. Let `G(E(R))` be the
minimum depth of such a cone schedule. Every actual sorting suffix is
one, so

```text
H(R) >= G(E(R)).
```

This preserves the shared matching constraints, unlike separately
checking each output's fan-in and each input's fan-out.

The script also requires each cone to determine its full rank decision,
not just its singleton differences. A further variant requires a monotone
extension on that cone. Its allowed supports must hit every directed cut
`x minus y` with `T_k(x)=1` and `T_k(y)=0`: otherwise projection would
put a positive point below a negative one. Hitting all such cuts is also
sufficient for a monotone extension, by upward closure of positive
projections. Through five wires, neither strengthening increases the
minimum joint cone depth beyond the singleton-incidence model. This is
finite evidence only.

### An actual one-layer inequality

For an actual layer `L` and its image `R'=L(R)`,

```text
G(E(R)) <= 1 + G(E(R')).
```

An edge of `R` differing only at coordinate `i` maps to an edge of `R'`
of the same rank, differing at one coordinate `j`. Monotonicity and
preservation of the number of ones give this one-coordinate difference.
The coordinate `i` lies in the layer's dependency cone of `j`.
Prepending this layer to any cone schedule satisfying `E(R')` therefore
satisfies every demand in `E(R)`. The finite benchmark checks this
inequality on all transitions, including 14,525 on five wires.

This is a derived structural inequality with a sound residual meaning,
but its initial value is too small to improve the asymptotic constant.

## 3. A concrete joint obstruction, with a short proof

The actual five-wire prefix

```text
[(1,2),(3,4)], [(0,1),(2,4)], [(1,2)]
```

has image

```text
{0,4,16,20,21,22,23,24,28,30,31},
```

using bit `i` for wire `i`. Its largest unrestricted cube has dimension
two. Its minimum determining-coordinate sizes, from low to high threshold,
are `(2,3,4,3,2)`, and input fan-out requirements are `(3,2,3,4,2)`.
Thus cube sorting, individual fan-in, and individual fan-out give at most
two layers. Yet the joint dependency bound is three, and three actual
comparator layers suffice.

The mandatory input sets at **output wires** `0,...,4` are

```text
{0,3}, {0,1,3}, {0,1,2,3}, {2,3,4}, {2,4}.
```

Suppose two cone layers could meet these demands. Output 2 needs four
distinct inputs, so its two first-layer cones must be disjoint pairs
covering `{0,1,2,3}`. Wire 4 must therefore be idle in the first layer:
including it in those pairs would consume one of the four available
positions without supplying a required input.

Output 3 needs input 4. It must therefore pair with wire 4 in layer two.
Output 4 also needs input 2, so the first-layer pair containing wire 3
must be `{2,3}`. The other pair is `{0,1}`.
To acquire all four inputs, wire 2 must pair with either 0 or 1 in layer
two. The remaining wire in `{0,1}` stays idle and never acquires input 3,
contradicting the mandatory sets of both outputs 0 and 1. Thus two layers
are impossible, irrespective of gate orientation or Boolean semantics.

An actual optimal suffix is

```text
[(1,3)], [(0,1),(2,3)], [(1,2),(3,4)].
```

Across all five-wire images, the joint bound improves on cube plus
individual fan-in on 23 images; **18** still improve after adding the
individual fan-out bound. Cube plus joint dependency is exact on all
44 four-wire images, but underestimates some five-wire images by one
layer. It remains a necessary relaxation, not a full characterization.

## 4. Coupled families that cubes alone miss

Consider the image consisting of `k` independently sorted blocks of
equal length `m`, with `k>=2` and `n=km`. Its largest unrestricted cube
has dimension exactly `k`: each sorted block admits one free boundary
bit, but cannot admit two independently arbitrary positions.

At total-weight threshold `T` in the interval
`m <= T <= n-m+1`, all `n` coordinates are mandatory. For each position,
choose its block's count so toggling that coordinate increases the count
by one, and choose the other blocks' counts to make the total `T-1`.
Those counts are available throughout the stated interval. Consequently
any merging suffix has depth at least `ceil(log_2 n)`, even if `k=2`.
This grows while the cube bound `D(2)=1` stays constant.

If a prefix independently sorts two original disjoint blocks of length
`n/2`, its depth is at least `D(n/2)`. Its image is the product of the
two sorted-block domains. The necessary suffix adds `log_2 n`
layers. Thus this is another restricted family with total asymptotic
coefficient at least `4.270559...`. It does not imply that an arbitrary
sorter must pass through two sorted large blocks.

## 5. Two limits that matter for the general target

### Cube and information costs cannot just be added

The candidate

```text
H(R) >= D(w(R)) + ceil(log_2(s(R)/w(R)))
```

where `w` is maximum cube dimension and `s=max s_k`, is false. After
the single four-wire gate `(2,3)`, `w=3`, `s=4`, and `D(3)=3`, so it
predicts four layers. The three-layer suffix

```text
[(0,1)], [(0,2),(1,3)], [(1,2)]
```

sorts this image. Gathering the additional information and sorting the
cube can happen in the same layers. There are 14 four-wire and 310
five-wire counterexamples to this exact finite candidate. These do not
rule out an asymptotic statement with an appropriate correction term.

Also, the maximum of cube and joint cone lower bounds can decrease by
two in a single five-wire layer. It is not itself a one-layer amortized
potential, even though the cone bound separately obeys the inequality above.

### Pure reachability cannot supply coefficient four

On `n=2^d` wires, `d` hypercube union layers make every cone contain
every input coordinate. Hence `G(E) <= log_2 n` for **every** incidence
matrix, and the same ceiling holds for the determining-set variants:
the full coordinate set always determines each rank monotonically.

To go beyond this ceiling, retain the AND/OR meanings of the shared
signals. A union gate gives both outputs the same cone; an actual
comparator gives a minimum and a maximum whose values and certificates
are coupled and whose sum is conserved. Monotone extensions chosen
independently at outputs omit precisely this constraint.

The next useful experiment should strengthen the joint cone state with
two-output logical feasibility on adjacent rank cuts, testing against
the exact completion benchmark. A successful asymptotic argument must
show that those constraints accumulate across scales rather than being
paid for by the same layers. Counting disjoint copies of the five-wire
obstruction is insufficient: they can all run in parallel.

## Reproduction and trust

```text
python -B lower-bound/experiments/scripts/kahale_image_difficulty.py --output docs/kahale-image-difficulty-results.json
```

The saved file contains every image, optimal prefix and suffix, support
families, cone witnesses, and additive-candidate counterexamples. Cone
catalogues have 2, 11, 189, and 9,152 states for widths 2 through 5.
All arithmetic and searches are exact standard-library Python. No Lean
changes, builds, new dependencies, or new axioms were introduced.
