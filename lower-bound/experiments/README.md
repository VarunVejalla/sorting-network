# Lower-bound experiments

This package preserves the remaining `AKS.Kahale` research modules that are
not required by the proved best endpoint.  It depends on `../best`, so shared
headline modules are not duplicated here.  Network and utility foundations are supplied by the transitive legacy
upper dependency; no copies of those foundations are retained here.

These files include proved lemmas, obstruction results, counterexamples, and
research infrastructure.  Their presence here does not claim a stronger
asymptotic lower bound than the theorem in `../best`.

The latest Python-first investigation is
[the structural low-rank barrier](../../docs/kahale-low-rank-barrier.md), following
[the certified quadratic-correction barrier](../../docs/kahale-pair-constraint-generation.md), following
[pair preimage corrections](../../docs/kahale-pair-correction.md), following
[the singleton-correction obstruction](../../docs/kahale-singleton-correction.md), following
[the capacity-lift obstruction](../../docs/kahale-capacity-lift.md), following
[singleton preimage capacities](../../docs/kahale-preimage-capacity.md) and
[amortized witness charges](../../docs/kahale-witness-charge.md), following
[shared comparator polarity](../../docs/kahale-joint-polarity.md), using
[residual image difficulty](../../docs/kahale-image-difficulty.md) and
[preparation charges and residual sorting problems](../../docs/kahale-certificate-preparation.md).
It gives exact finite charge certificates and additive-family barriers;
signed nonlinear interactions recover the small sorting-depth benchmark.
These do not
improve the universal checked lower-bound coefficient.

Build all preserved experiment modules with:

```sh
lake build
```
