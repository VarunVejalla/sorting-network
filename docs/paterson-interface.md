# Paterson construction: interface audit

For the current local file map, verified milestones, and the path to a limsup
bound, start with [the research index](research-index.md). This document gives
the detailed interface and source audit.

Status: the restricted-halver theorem, its uniform probability estimate, a shared depth-263 first-level primitive, the injective local-input bridge, a supported-range separator interface, and a concrete five-level network of depth at most 989 are formalized in Lean. The network's supported-range separator property is now proved when its arity is divisible by 32. Odd-size separator correctness and the top-level sorting bound are not yet formalized.

## Formal proof components

- `AKS/Halver/MatchingCount.lean` counts permutations carrying a fixed `X` into a fixed `Y`, proves the sampling-without-replacement inequality, and bounds both orientations of a `c`-matching event by `(|Y|/m)^(c*|X|)`.
- `AKS/Halver/PatersonCorrectness.lean` proves that the absence of small traps implies the actual two-sided restricted-halver contract for the comparator network.
- `AKS/Halver/PatersonExistence.lean` combines these results. `exists_halver_of_size_bound` produces a network of depth at most `c` from a covering family of size pairs and the explicit inequality `2 * sum_(r,s) choose(m,r) * choose(m,s) * (s/m)^(r*c) < 1`.
- `AKS/Halver/PatersonEntropy.lean` proves the sharp binomial entropy estimate, including its square-root prefactor, from Mathlib's Stirling sequence. `failure_term_le` bounds an individual size-pair contribution by `(s/m)^r / (pi*r)` when its entropy budget holds.
- `AKS/Halver/PatersonMonotonicity.lean` proves the required monotonicity of Paterson's entropy-depth ratio in both parameters. `AKS/Halver/PatersonDepthBridge.lean` uses it to discharge the entropy budget and sharp per-witness failure bound from the advertised depth formula.
- `AKS/Halver/PatersonCollapsedWitnesses.lean` formalizes the appendix's reduction to one maximal-total witness per rounded error count, with all floor/endpoint cases and automatic exclusion of impossible traps. `exists_halver_of_collapsed_tail_bound` isolates the remaining finite real-valued tail sum. `AKS/Halver/PatersonWitnesses.lean` retains the simpler one-per-total-size intermediate reduction.
- `AKS/Halver/PatersonTail.lean` bounds that sum by `3/(2*pi)` for every positive side arity, using the two small- and large-`epsilon*m` cases. `exists_paterson_halver_all_arities` proves Paterson's all-arity restricted-halver theorem with depth at most the ceiling of the advertised entropy formula, including the zero-wire case.
- `AKS/Halver/PatersonSimultaneous.lean` proves that one matching sequence meets two restricted-halver contracts whenever the union of the two trap families has total probability below one. `AKS/Halver/PatersonJointTail.lean` proves the missing joint bound, using a geometric-series estimate for the small supported fraction. `exists_paterson_first_level_all_arities` supplies one depth-263 network for both first-level contracts at every side arity, including zero.
- `AKS/Separator/PatersonInjective.lean` proves that both restricted-halver guarantees remain valid when a local comparator block is fed by an injective selection from a larger ambient input. This is the local-input bridge needed by a Paterson-specific separator induction.
- `AKS/Separator/PatersonDefs.lean` states the supported-range separator contract that matches Paterson's smaller stranger cohort and proves the first-level bridge. `AKS/Separator/PatersonFamily.lean` selects noncomputable networks at every side arity. `AKS/Separator/PatersonConstruction.lean` assembles the five differently parameterized levels, proves each selected local stage meets its supported-range contract, and bounds the composed network's depth by 989.
- `AKS/Separator/PatersonNear.lean` proves both local near-stranger estimates using only restricted-halver hypotheses. `AKS/Separator/PatersonStep.lean` proves the two-sided supported-range induction step for even chunks. `AKS/Separator/PatersonPrefix.lean` applies it across all five actual stages: `separatorNetwork_supported_of_dvd32` proves the composed network's supported-range guarantee for `32 ∣ n`. The theorem is restricted to this divisibility case; it does not cover odd-size blocks or the stronger first-level good-value propagation required in the bag invariant.
- `AKS/Separator/PatersonCertificate.lean` identifies the five-stage error with `patersonTailError` and combines the supported-range theorem and depth-989 bound for the same selected network. Its divisibility hypothesis remains `32 ∣ n`.
- `AKS/Separator/PatersonOdd.lean` proves that padding an odd left block with a virtual maximum preserves its restricted initial-cohort bound with no additive error or depth increase. `AKS/Separator/PatersonFlip.lean` proves wire-reversal/value-duality and that flipping preserves both restricted-halver guarantees. `AKS/Separator/PatersonOddFinal.lean` then proves the symmetric virtual-minimum/right-side odd-block bound, again with no added error or depth. These one-sided gadgets are not yet assembled into an arbitrary-size five-level separator.
- `AKS/Bags/PatersonParams.lean` checks exact parameter arithmetic and both interior stranger inequalities, including the correction discussed below.
- `AKS/Bags/PatersonNumerics.lean` proves rational enclosures for logarithms and certifies the six rounded local depth budgets: 262, 263, 155, 167, 187, and 217. Their prescribed combination is at most 989 (`separatorDepthBudget_le_989`). This proves the numerical formula, not the existence of the separator.
- `AKS/Halver/PatersonAxioms.lean` checks that these results depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The new modules are imported by `AKS.lean` and checked by `lake build AKS`.

The all-arity restricted-halver existence theorem is now unconditional under Paterson's stated parameter range. It is nonconstructive: the matching layers are selected by finite probabilistic counting, as in the paper. This completes the halver theorem, not the sorting-network theorem.

Primary source: M. S. Paterson, *Improved Sorting Networks with O(log N) Depth*, Algorithmica 5 (1990), 75–92. The University of Warwick archive hosts the paper at <https://wrap.warwick.ac.uk/id/eprint/60785/>. The downloaded version is a 23-page archive PDF including front matter; the article's numbered pages 1–17 begin at PDF page 3.

## What the paper's improvement actually changes

Paterson keeps the AKS/Seiferas-style bag tree and stranger-counting invariant, but improves the separator construction. Its key local primitive is an “(ε,α)-halver”: on `2m` wires split into two sides of size `m`, it must route the extreme `k` values with at most `ε k` errors only for `k ≤ α m`.

The appendix proves that for every `0 < ε < 1/2`, `0 < α ≤ 1`, and every positive `m`, such a halver exists with depth at most

```text
ceil(1 + (h(εα) + h((1-ε)α))
         / (-εα ln((1-ε)α)))
```

where `h(x) = -x ln x - (1-x) ln(1-x)` is binary entropy using natural logarithms. The ceiling and explicit all-size statement matter: the bag network applies local gadgets at small as well as large arities. Paterson obtains this bound from a probabilistic count over sequences of perfect matchings between the two sides. The paper explicitly notes that this proof does **not** produce an explicit halver network.

The separator uses several restricted halvers with different supported fractions. For the reported `p = 5` choice, define

```text
eta = 4 * mu * delta * A^2 / (1 - 4 * delta^2 * A^2) + 1 / (4 * A^2 - 1)
C(alpha, e) = ceil(1 + (h(e*alpha) + h((1-e)*alpha))
                         / (-e*alpha*ln((1-e)*alpha)))
```

Then the separator depth is bounded by

```text
max(C(2*mu, delta_1), C(1 - eta - 2*mu, delta_0))
  + C(4*mu, delta_2) + C(8*mu, delta_3)
  + C(16*mu, delta_4) + C(32*mu, delta_5).
```

This level-dependent use of restricted halvers is the source of the large improvement; replacing each with an ordinary full-range halver loses the advertised constant.

## Fit with this Lean repository

`AKS/Halver/Defs.lean` defines `HalverFamily ε`, whose property is required for every extreme-set size up to half the wires. `AKS/Separator/FromHalver*.lean` builds its prefix-doubling separator from that full-range guarantee. Paterson's restricted guarantee therefore cannot satisfy this interface at the useful depth without strengthening the interface in a way that throws away the α-dependent gain.

The bag-tree architecture is related, but its parameter constraints and separator interface must be compared theorem by theorem. The repository's `Params` are the later Seiferas constraints (`γ`, `ε`, `ν`, `A`) and should not be assumed to encode Paterson's parameter set or rounding argument automatically.

There is already a concrete warning against a direct parameter substitution. Paterson's recurrence gives `v = 421/608`. If the repository's `γ` is identified with the per-fringe fraction `λ/2 = 1/32`, its `Params.hC3` condition would require

```text
v ≥ 4 * γ * A + 5 / (2 * A) = 19/32 + 10/19 > 1.12,
```

which is incompatible with `v = 421/608 < 0.70`. Thus the current `Params` proof does not directly accept Paterson's reported choices under that natural mapping. This must be resolved by a different parameter correspondence or by adapting/formalizing Paterson's own bag-capacity argument.

There are two viable integration directions to investigate:

1. Add a `RestrictedHalverFamily ε α`, prove Paterson's all-size existence theorem, then build and prove a Paterson separator using the level-specific α values. Reuse the current bag-tree theorem only after proving that its separator contract is exactly the one Paterson supplies and that the parameter hypotheses align.
2. Formalize Paterson's own bag update, boundaries, integer rounding, and depth accounting. This is more independent, but avoids forcing a mismatched local interface into the existing development.

The existence theorem can in principle be turned into a noncomputable family by choice. A computable family could also be obtained by finite search once a finite size bound on the bipartite comparator layers is formalized, but that would not yield a practical construction algorithm. The current top-level `network` is computable, so this distinction must be explicit in any result claimed to preserve the repository's construction properties.

## Status of the `<6100 log_2 N` figure

In Section 8, Paterson reports a choice described approximately by `p = 5`, `A = 4.75`, `μ = 1/50`, `δ = 1/57`, and reciprocal level errors `62, 199, 110, 109, 106, 90`. Substituting these rationals into the paper's formulas gives the following useful numerical audit (ordinary floating-point evaluation, not a formal certificate):

| Quantity | Approximate value |
|---|---:|
| Bag shrink factor `v = 2(1/16)A + (1-1/16)/(2A)` | 0.69243421 |
| Stages per `log_2 N`, `ln(2A)/(-ln v)` | 6.12526325 |
| `eta` from Paterson's invariant bound | 0.04377591 |
| First-level supported fraction `1 - eta - 2*mu` | 0.91622409 |
| Separator depth from the level-specific `C(α,ε)` bounds, after rounding each to an integer | 989 |
| Product using the coarser bound `6.15 * 989` | 6082.35 |

This explains the paper's `<6100` headline and gives a plausible formal target with modest numerical slack. It still does not finish the theorem: the exact first-level separator formula, integer bag-size rounding, finite startup/root splitting and cleanup costs, and the conversion from the asymptotic stage ratio to a uniform bound all need formal treatment. In particular, a coefficient close to 6100 cannot absorb an arbitrary `O(1)` term for every input size without a separate small-size argument.

Accordingly, `<6100` is a source-backed target, not yet a formal consequence of the current repository or of this note. The exact parameter arithmetic, numerical depth bounds, and supported-range separator theorem for `32 ∣ n` are checked. The arbitrary-size local separator and global bag construction still need their correctness proofs.

The rounded numerical upper bound of 989 is formally certified in `PatersonNumerics.lean`. The table above remains a useful decimal audit of the formulas. The same first-level matching sequence must satisfy both restricted-halver contracts; taking the maximum of two separate existence bounds alone would not establish this. That simultaneous obligation is discharged by `PatersonJointTail.lean` and `exists_paterson_first_level_all_arities`.

## Correction to the approximate parameter table

The literal parameter choices with `lambda = 1/16` fail Paterson's two interior stranger inequalities. Lean proves both failures in `patersonUnadjusted_tail_fails` and `patersonUnadjusted_first_fails`. The deficits are approximately `2.146e-5` and `4.555e-6`, respectively. Thus the unadjusted `v = 421/608` must not be used as a valid instantiation of the bag argument.

The rational replacement `v = 693/1000`, with corresponding `lambda = 11167/178500`, strictly satisfies both interior inequalities, and Lean proves its ideal stage ratio is still below `123/20 = 6.15`. This resolves those arithmetic failures. It does not prove that bag rounding, root splitting, and boundary processing fit the remaining depth allowance.

## Remaining proof obligations

1. Assemble the two proved one-sided odd-block gadgets into a five-level supported-range separator for arbitrary local sizes. The first-level good-value contract is available locally but must also be threaded through the bag proof; the current `IsSeparator` contract is too strong for the level-specific supported fractions.
2. Formalize Paterson's bag transitions and invariants, cold storage, partial levels, integer rounding, root splitting, and cleanup. The current Seiferas parameter theorem cannot supply these steps directly.
3. Combine the verified numerical budgets with the actual scheduler and boundary costs to prove the final bound, with a separate small-size argument if needed.

For this project's limsup objective, it suffices to prove a sorting bound
`C * log_2 n + o(log n)`. Constant startup and boundary costs do not change the
coefficient. The stage count must retain its real asymptotic coefficient;
rounding `6.15` itself up to `7` would lose the proposed `<6100` target.

## Relevant source locations

- Article §§3 (numbered pp. 3–4): ordinary halver and separator definitions.
- Article §§4–§6 (numbered pp. 5–11): bag tree, stranger invariant, boundary handling, and finishing argument.
- Article §§7 (numbered pp. 12–13): integer rounding and odd-size halvers.
- Article §§8 (numbered pp. 14–15): restricted halver theorem, refined separator depth, and the reported parameter choices.
- Appendix (numbered pp. 18–21): probabilistic existence proof and entropy bound.
