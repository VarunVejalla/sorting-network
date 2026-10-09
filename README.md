# Sorting-network depth bounds in Lean

This project studies explicit bounds on the minimum depth `D(n)` of a sorting
network on `n` inputs using binary comparators. The research goals are to refine

$$
\liminf_{n\to\infty}\frac{D(n)}{\log_2 n}
\quad\text{and}\quad
\limsup_{n\to\infty}\frac{D(n)}{\log_2 n}.
$$

The project includes upper-bound constructions and a formalized Kahale lower bound.
The project builds on [Geoffrey Irving's AKS formalization](https://github.com/girving/aks)
in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Current verified upper bound

The strongest completed upper bound is the Chvátal construction in the separate
[chvatal-1830 package](chvatal-1830/README.md). Lean proves

```text
D(n) <= 1830 * log_2 n - 58657   for n >= 64^7 = 2^42.
limsup D(n)/log_2 n <= 1830.
```

The theorem endpoints are

```lean
SortingDepth.minimum_depth_le_1830_logb
SortingDepth.limsup_minimum_div_logb_le_1830
```

See [Chvatal1830Final.lean](chvatal-1830/AKS/Bounds/Chvatal1830Final.lean).
The proof includes the separators, tree scheduler, actual comparator execution,
rank invariants, final block sorting, and the global depth calculation. It follows
Chvátal's *Lecture Notes on the New AKS Sorting Network*, DCS-TR-294 (1992).
Published arguments are formalized; paper results are not assumed as axioms.

The verified pruning checkpoint passed the full package build and both
headline axiom guards on 2026-10-09. See
[the verification record](chvatal-1830/BUILD_STATUS.md).
This reproduces a published construction; it is not a new published-record bound.

### Bound for every input size

The completed rounded Paterson construction remains available in the main package:

```text
D(n) <= 6991 * Nat.clog 2 n                  (every natural n).
2 * D(n) <= 13981 * Nat.clog 2 n + 13979.
limsup D(n)/log_2 n <= 6990.5.
```

For `n >= 1`, `Nat.clog 2 n` is `ceil(log_2 n)`; the finite statements also cover
`n = 0`. See [PatersonTight.lean](AKS/Bounds/PatersonTight.lean).
The older million-coefficient proof is retained in
[Paterson.lean](AKS/Bounds/Paterson.lean).

## Verified lower bound

Lean also proves

$$
\liminf_{n\to\infty}\frac{D(n)}{\log_2 n}
\ge \frac{1}{1-\log_2((1+\sqrt5)/2)} \approx 3.270559454.
$$

This reproduces the published Kahale et al. bound. The proof includes all
combinatorial ingredients and the connection to the repository's network depth.
See [the lower-bound proof map](docs/kahale-lower-bound.md). Build it separately
with `lake build AKS.Kahale`.

## Paterson construction details

The proof uses the depth-989 five-level separator and a rounded bag allocation
with `A = 19/4`, `mu = 199/10000`, `delta = 1/57`, and `nu = 707/1000`.
It includes the actual comparison stages, root-region sorting and rebuild,
child allocations and stranger invariants, and a terminating recursive forest.
All rank permutations produce one fixed output arrangement. A fixed correction
network sorts that arrangement in depth at most one per logarithmic level;
the permutation principle then establishes sorting for arbitrary ordered inputs.

Every comparison, root sort, terminal sort, and correction is included in

```text
2 * depth(correctedForest k) <= 13981 * k + 13979.
```

Bitonic sorting covers the finite startup range in the all-n coefficient-6991
bound. The separator family and final networks are selected classically:
these are existence theorems, not an executable network-generation algorithm.
Published arguments guide the proofs; no paper theorem is imported as an axiom.
This improves the repository's former million bound, not the published best bounds.

Start with [the research index](docs/research-index.md) for the proof map and
[the root split argument](docs/paterson-root-split-design.md) for the construction.

## Repository map

| Path | Contents |
| --- | --- |
| [AKS/Bounds/](AKS/Bounds/) | Minimum-depth definition, all-arity bounds, and asymptotic theorems |
| [AKS/Paterson/](AKS/Paterson/) | Completed rounded bag construction |
| [chvatal-1830/](chvatal-1830/README.md) | Self-contained Lean package: `D(n) ≤ 1830 log₂ n − 58657` for `n ≥ 64^7` and `limsup D(n)/log₂ n ≤ 1830` (Chvátal DCS-TR-294) |
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

Build the strongest upper bound separately:

```sh
cd chvatal-1830
lake build
lake build AKS.Bounds.Chvatal1830Axioms
```

The main package and the Chvátal package have separate build roots and retain
identical `AKS` module names. Building the main package does not check Chvátal.
The latest verification above concerns the Chvátal package; earlier main-package
verification is recorded in the research notes.

## Proof trust and reproducibility

The main results depend only on Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. Guarded axiom checks are in
[Chvatal1830Axioms.lean](chvatal-1830/AKS/Bounds/Chvatal1830Axioms.lean) and
[PatersonTightAxioms.lean](AKS/Bounds/PatersonTightAxioms.lean).
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
completed rounded bag construction, the Chvátal 1830 construction, and the Kahale
lower-bound formalization.

Principal mathematical sources:

- Ajtai, Komlos, Szemeredi (1983), *An O(n log n) sorting network*.
- Seiferas (2009), *A simpler proof that an O(n log n) sorting network sorts in O(n log n) time*.
- Paterson (1990), *Improved sorting networks with O(log N) depth*.
- Margulis (1973) and Gabber, Galil (1981), explicit expander constructions.
- Batcher (1968), *Sorting networks and their applications*.
- Chvátal (1992), *Lecture Notes on the New AKS Sorting Network*, DCS-TR-294.
- Kahale et al. (1995), the sorting-network depth lower bound; see
  [the formalization notes](docs/kahale-lower-bound.md).

Source discussions and proof-specific references are in the Lean modules and
[docs/](docs/). This repository retains the upstream [Apache 2.0 license](LICENSE).
