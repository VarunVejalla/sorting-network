# A structural barrier to charges confined to low input ranks

## Main conclusion (2026-10-12)

The recent zero-output-fiber charges cannot by themselves improve Kahale's
coefficient. They read only global input weights at most three. Any
standalone potential determined by those slices, with unit parallel-layer
drop and the sorted endpoint value, has initial-minus-terminal value at most
`3 ceil(log_2 n)`.

This is a derived general mathematical argument, with exact finite Python
checks, not a Lean theorem. It is not a barrier to pair information across
all ranks, to a joint charge using Kahale's other information, or to
history-dependent preparation arguments.

## Low-rank extraction construction

For any `m` wires, a balanced maximum tournament has at most
`ceil(log_2 m)` parallel layers and puts the maximum at wire `m-1`.
Pair adjacent active representatives, retain each pair's larger-index
representative, and leave an unpaired representative active. Every layer is
a matching. Each representative carries its group's maximum; the final
representative is the largest wire index.

Run that tournament on all `n` wires, then the first `n-1`, and so forth,
for `r` rounds. The last `r` wires contain the largest `r` values in order.
Hence every Boolean input of weight at most `r` is fully sorted. The depth is

\[
 \sum_{j=0}^{r-1}\lceil\log_2(n-j)\rceil
 \le r\lceil\log_2 n\rceil\qquad(1\le r\le n).
\]

No claim is made that the other inputs are sorted.

## Potential ceiling

Let `T_r(F)` be the complete labeled action of a comparator prefix `F` on
all inputs of weights `0,...,r`. Suppose a potential depends only on this
action (or any summary of it), and its drop along every actual parallel
layer is at most one. The extraction prefix above has exactly the same
`T_r` as a fully sorted network. Telescoping along that prefix gives

\[
 P(\mathrm{identity})-P(\mathrm{sorted})
 \le r\lceil\log_2 n\rceil.
\]

This applies even when the summary keeps labeled preimages, normalized
masses, arbitrary nonlinear functions, and overlaps within those slices.
The limitation is the input ranks retained, rather than the functional form.
It assumes the layer inequality applies to actual prefixes, as in our
feasibility screens. Such prefixes can always be extended to a full sorter.

## Application to the current work

The ten-term charge tests projected witness ranks 1, 2, and 3 after fixing
all other outputs to zero. Weight preservation means these witnesses come
from global inputs of those same weights. Its correction uses singleton and
pair input preimages. Consequently the combined state depends only on
`T_3`. Any shared collection of such zero-output-fiber charges still has this
limitation if it reads no additional input ranks.

Thus even finding a universal normalized nonlinear correction in the current
state would not give a standalone coefficient above 3, below the verified
Kahale coefficient approximately 3.270559454. It could still contribute to
a joint argument if additional information proves that its preparation and
Kahale's costs cannot be paid simultaneously. That nonoverlap is not proved.

## Pair-terminal data can hide arbitrarily large residual work

There is also an explicit family illustrating information loss. Compare
each wire `i<n-1` against wire `n-1`, one at a time. Then compare every
`i<n-2` against wire `n-2`, one at a time. All weight-zero, one, and two
inputs now have exactly their fully sorted outputs, including labeled
preimages. Nevertheless the full image is

\[
 \{0,e_{n-1}\}\ \cup\
 \{x:x_{n-2}=x_{n-1}=1\}.
\]

Every output of weight at least two has both top wires equal to one.
Conversely inputs initially having those two wires equal to one are left
unchanged by the prefix, so the entire remaining `(n-2)`-cube survives.
The required suffix depth is exactly `D(n-2)`: sorting the first `n-2` wires
suffices; restricting to the fixed-two-one cube and removing constant wires
gives the reverse inequality. The usual constant-removal argument retains
at most one comparator per pair of surviving wires in each layer.

This star construction has linear prefix depth. It demonstrates residual
information loss; the logarithmic tournament construction above supplies
the separate asymptotic potential ceiling.

## Checks and revised next target

[Script](../lower-bound/experiments/scripts/kahale_low_rank_barrier.py) checks
32 selector cases on 2 through 12 wires (1547 relevant inputs), the star
image identity on 4 through 10 wires, and exact small completion distances.
On five wires, a prefix with terminal singleton/pair data still needs three
more layers. [Results](kahale-low-rank-barrier-results.json).

The next meaningful target is **conditional pair routing at baselines of
varying Hamming weights**, including central weights, with compatibility
between neighboring baselines. This avoids confining the state to global
weights at most three. Pair capacities alone must be augmented by a charge
for overlap and preparation; the earlier activation-scale and sorted-block
obstructions remain applicable. Further fitting of zero-baseline-only
corrections should not be treated as the main route to an improved constant.
