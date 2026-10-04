# Sorting-network depth bounds in Lean

This project studies explicit bounds on the minimum depth `D(n)` of a sorting
network on `n` inputs using binary comparators. The research goals are to refine

$$
\liminf_{n\to\infty}\frac{D(n)}{\log_2 n}
\quad\text{and}\quad
\limsup_{n\to\infty}\frac{D(n)}{\log_2 n}.
$$

The current focus is improving the upper bound through Paterson's construction.
The project builds on [Geoffrey Irving's AKS formalization](https://github.com/girving/aks)
in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Current verified result

For every natural number `n`, Lean proves

```text
D(n) <= 10^6 * Nat.clog 2 n.
```

For `n >= 1`, `Nat.clog 2 n` is `ceil(log_2 n)`. The formal statement also handles
`n = 0`. Consequently,

$$
\limsup_{n\to\infty}\frac{D(n)}{\log_2 n}\le 10^6.
$$

The endpoints in [AKS/Bounds/Paterson.lean](AKS/Bounds/Paterson.lean) are:

```lean
SortingDepth.minimum_depth_le_million
SortingDepth.limsup_minimum_div_logb_le_million
```

This complete proof combines full-support Paterson halvers, prefix-doubling
separators, and the established Seiferas bag scheduler. It covers small inputs,
arbitrary arities, rounding, and final cleanup. The scalar coefficient certificate
is `999189 = 14 * 71370 + 9 < 10^6`.

The networks are selected classically from formally proved existence results.
This is a sorting-network existence bound, rather than an executable search
algorithm. The original executable MGG-based constructions remain available.
This improves the bound formalized in this repository; it is not a new
improvement over published mathematical bounds.

## Tighter Paterson construction: work in progress

The refined Paterson bag construction is **not yet a complete sorting theorem**.
Verified components include restricted-halver existence, a five-level separator
of depth at most 989 for arities divisible by 32, local stranger estimates,
concrete interior invariant preservation under explicit size and rank-balance
hypotheses, padded partial-bag gadgets, and lattice rounding and routing identities.
The current candidate budget is `989 * 6.5 + 561 = 6989.5` per logarithmic
input level; its global construction and operation counts remain unproved.

The implemented mixed full/partial comparison stage now preserves the complete
stranger invariant. The actual repeated network has depth at most `989*t`
while the root capacity remains in its allowed window. Root split groundwork
includes the actual upper-region size, exact deep-subtree counts, global-half
purity, and sorted-bin error estimates.

The main remaining steps are:

- Construct the root rebuild and split into independent smaller trees, preserving
  allocation and stranger invariants.
- Prove forest termination, final sorting, and the required wire ordering or correction.
- Account for every comparison, root sort, terminal sort, and correction, then
  derive the minimum-depth and limsup bounds.

The local depth-989 separator alone does not establish the tighter global bound.
Published arguments guide the formalization; paper results are not assumed as
new Lean axioms.

Start with [the research index](docs/research-index.md) for theorem endpoints,
precise proof boundaries, parameters, and focused build commands.
[The interface audit](docs/paterson-interface.md) provides more detail.

## Repository map

| Path | Contents |
| --- | --- |
| [AKS/Bounds/](AKS/Bounds/) | Minimum-depth definition, all-arity bounds, and asymptotic theorems |
| [AKS/Paterson/](AKS/Paterson/) | Refined bag construction in progress |
| [AKS/Halver/](AKS/Halver/) | Paterson halvers, probabilistic existence, and expander-based halvers |
| [AKS/Separator/](AKS/Separator/) | Generic and Paterson separator constructions |
| [AKS/Bags/](AKS/Bags/) | Verified Seiferas scheduler and shared bag infrastructure |
| [AKS/Seiferas.lean](AKS/Seiferas.lean) | Original executable MGG-based sorting construction |
| `AKS/Sort/`, `AKS/Bitonic/` | Comparator networks, sorting correctness, and bitonic cleanup |
| `AKS/Graph/`, `AKS/MGG/`, `AKS/ZigZag/` | Expander constructions and spectral proofs |
| [docs/](docs/) | Current research notes, source material, and historical visualization |
| [AKS_CODEX_HANDOFF_2026-09-27/](AKS_CODEX_HANDOFF_2026-09-27/) | Preserved historical handoff; some claims are superseded |
| `Random/`, `rust/`, `scripts/` | Optional certificates, experiments, and maintenance tools |

The `AKS` module and package names are retained for compatibility with the
inherited formalization.

## Setup and build

Install [elan](https://github.com/leanprover/elan); the repository's
`lean-toolchain` selects the required Lean version. From the repository root:

```sh
lake exe cache get
lake build AKS
```

Use `lake build AKS` for the main formalization. The default `lake build` also
includes optional certificate targets that can download multi-gigabyte data.

The complete `AKS` build passed at the current mathematical milestone. The
source audits found no `sorry`, declared axioms, or `native_decide` in `AKS/`.

## Proof trust and reproducibility

The main results depend only on Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. Guarded axiom checks for the new bound are in
[AKS/Bounds/PatersonAxioms.lean](AKS/Bounds/PatersonAxioms.lean).
The main proof does not require the optional expander certificate data.

The optional `Random/` certificate path has a separate trust boundary involving
native evaluation and C FFI; see [docs/trust.md](docs/trust.md).
The inherited comparator challenge and dependency visualization concern the
original construction and should not be treated as audits of the new bound.

## Working on the project

[AGENTS.md](AGENTS.md) contains the shared project instructions for Claude,
Codex, Cursor, and other agents. Current source declarations and the research
index take precedence over historical handoff status reports.

## Mathematical sources and attribution

The inherited AKS, MGG, and Seiferas formalization is credited to the
[upstream project](https://github.com/girving/aks). Local work extends it with
Paterson halver proofs, explicit minimum-depth and asymptotic bounds, and the
refined bag construction in progress.

Principal mathematical sources:

- Ajtai, Komlos, Szemeredi (1983), *An O(n log n) sorting network*.
- Seiferas (2009), *A simpler proof that an O(n log n) sorting network sorts in O(n log n) time*.
- Paterson (1990), *Improved sorting networks with O(log N) depth*.
- Margulis (1973) and Gabber, Galil (1981), explicit expander constructions.
- Batcher (1968), *Sorting networks and their applications*.

Source discussions and proof-specific references are in the Lean modules and
[docs/](docs/). This repository retains the upstream [Apache 2.0 license](LICENSE).
