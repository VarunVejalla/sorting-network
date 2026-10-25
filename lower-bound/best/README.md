# Best proved lower bound

This standalone Lean package contains the dependency closure of the checked
Kahale endpoint
`SortingDepth.liminf_minimum_div_logb_ge_kahale`:

```text
liminf (D(n) / log₂ n) ≥ 1 / (1 - log₂ φ).
```

`AKS.Bounds.Minimum` exposes `D(n)` from the local legacy upper-bound package.
This dependency is mathematically relevant to the chosen real-valued `liminf`:
Mathlib requires a boundedness premise, discharged here by the existing
logarithmic-depth sorting construction.  The Kahale finite inequality itself does
not use that upper construction.

Build and audit the headline result with:

```sh
lake build AKS.Bounds.KahaleAxioms
```

The copied Kahale proof sources are unchanged from the repository root.  The
shared legacy package supplies the generic asymptotic lemma and its logarithmic
upper-bound corollary; this package owns the Kahale finite and liminf endpoints.

## Upper-bound-free statements (LB-11)

`AKS.Bounds.KahaleUnconditional` restates the asymptotic bound using only the
finite Kahale inequality:

- `SortingDepth.eventually_mul_logb_le_minimum`: for every
  `c < 1 / (1 - log₂ φ)`, eventually `c · log₂ n ≤ D(n)`;
- `SortingDepth.ereal_liminf_minimum_div_logb_ge_kahale`: the same `liminf`
  bound in `EReal`, where no boundedness premise is needed;
- `SortingDepth.liminf_minimum_div_logb_ge_kahale_of_cobounded`: the real
  `liminf` bound with the `IsCoboundedUnder (· ≥ ·)` premise as a hypothesis.

`AKS.Bounds.FiniteLowerAxioms` checks their axioms and checks that their
constant closures avoid the legacy `minimum_depth_le` (the old real headline
does not).  `D(n)` is still the legacy `Nat.find` definition, whose existence
witness is the bitonic network.

## Explicit finite bounds (LB-01)

`AKS.Bounds.FiniteLower` proves, for every `n`,

```text
SortingDepth.minimum_ge_max_bounds :
  max (⌈lg n⌉) (max (countingBound n) (kahaleBound n)) ≤ D(n)
```

where `countingBound n = ⌈⌈lg n!⌉ / ⌊n/2⌋⌉` (from `n! ≤ 2^(D(n)·⌊n/2⌋)`:
each comparator is at most two-to-one on inputs, and each parallel layer has at
most `⌊n/2⌋` comparators) and `kahaleBound n` is the least `d` with
`n · fib(d+1) ≤ 2^(d+1) (d+1)^2`.  The fan-in bound comes from `n ≤ 2^depth`.
`two_mul_sub_two_le_minimum_two_pow` gives `D(2^k) ≥ 2k - 2` for `k ≥ 2`
(via `n! ≥ nⁿ/eⁿ` and `e² < 8`), and `minimum_two_pow_sixteen_ge` gives
`D(2^16) ≥ 30`.  Check with `lake build AKS.Bounds.FiniteLowerAxioms`.
