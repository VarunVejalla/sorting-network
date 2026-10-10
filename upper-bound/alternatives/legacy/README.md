# Alternative upper constructions

This standalone package preserves the completed rounded Paterson construction
and older Seiferas/MGG infrastructure. It is outside the current best package.

The Paterson endpoints in `AKS/Bounds/PatersonTight.lean` give the all-n bound
`D(n) <= 6991 * Nat.clog 2 n` and asymptotic coefficient 6990.5.
The older million-coefficient Paterson and much larger Seiferas bounds remain
available as historical constructions and reusable lemmas.

```sh
cd upper-bound/alternatives/legacy
lake build AKS.Bounds.PatersonTightAxioms
```

Mathlib is shared from `../../../.lake/packages`. This package keeps its own
AKS definitions; build it separately from `upper-bound/best`. The lower and
limit packages use this legacy model through explicit dependencies.
`scripts/` holds alternative-construction experiments; `rust/` retains historical
bag/scheduler probes. Neither is needed for the Chvátal best build.

`Challenge.lean` and `challenge.json` retain the original comparator challenge.
The old root-AKS dependency graph analyzer and sibling-native simulation are in
`scripts/`; run `scripts/dead --dump` from this package directory so it loads
this package's AKS modules.
