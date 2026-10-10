# Lower-bound experiments

This package preserves the remaining `AKS.Kahale` research modules that are
not required by the proved best endpoint.  It depends on `../best`, so shared
headline modules are not duplicated here.  Network and utility foundations are supplied by the transitive legacy
upper dependency; no copies of those foundations are retained here.

These files include proved lemmas, obstruction results, counterexamples, and
research infrastructure.  Their presence here does not claim a stronger
asymptotic lower bound than the theorem in `../best`.

Build all preserved experiment modules with:

```sh
lake build
```
