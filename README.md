# Sorting-network depth bounds in Lean

This project studies minimum binary-comparator sorting-network depth `D(n)`:
`liminf D(n)/log_2 n` and `limsup D(n)/log_2 n`. It builds on
[Geoffrey Irving's AKS formalization](https://github.com/girving/aks) and Mathlib,
using Lean 4.29.0-rc4.

## Workstreams

| Path | Purpose |
| --- | --- |
| [upper-bound/best](upper-bound/best/README.md) | Current Chvátal construction: coefficient 1770 |
| [upper-bound/experiments](upper-bound/experiments/README.md) | Candidate improvements and optional expander certificates |
| [upper-bound/alternatives/legacy](upper-bound/alternatives/legacy/README.md) | Completed Paterson and older Seiferas constructions |
| [lower-bound/best](lower-bound/best/README.md) | Kahale lower bound: approximately 3.270559454 |
| [lower-bound/experiments](lower-bound/experiments/README.md) | Lower-bound research beyond the published endpoint |
| [research/limit-existence](research/limit-existence/README.md) | Conditional convergence, amplification, and repair research |
| [docs](docs/research-index.md) | Proof maps and mathematical notes |
| [archive](archive/README.md) | Historical scaffolding and preserved handoffs |

`best` packages are promotion destinations. Keep exploratory Lean changes in
separate packages until correctness, depth, and axiom dependencies are checked.
Packages use overlapping AKS module names and are built separately.

## Current bounds

The upper endpoint proves

```text
D(n) <= 1770 * log_2 n - 56497   for n >= 2^42
limsup D(n)/log_2 n <= 1770
```

The lower endpoint proves

```text
liminf D(n)/log_2 n >= 1/(1-log_2((1+sqrt(5))/2)) ≈ 3.270559454
```

These reproduce published constructions and lower-bound arguments. Paper
results are proved locally, not imported as axioms. Headline guards permit
only `propext`, `Classical.choice`, and `Quot.sound`.

The alternative Paterson construction retains the all-input-size bound
`D(n) <= 6991 * Nat.clog 2 n`, and asymptotic coefficient 6990.5.

## Building

The root Lake project maintains the shared Mathlib cache and has no default
proof target. Build the workstream you need:

```sh
# Optional initial dependency download, from repository root:
lake exe cache get

cd upper-bound/best
lake build
lake build AKS.Bounds.Chvatal1830Axioms

# In a separate shell, from repository root:
cd lower-bound/best
lake build
```

See package READMEs for endpoint guards and optional targets. Expander certificate
examples use native evaluation and C FFI; they are isolated from the best proofs
and are not built by default.

See [the reorganization verification](docs/reorganization-verification.md) for
the migration checks completed so far and the checks still pending.

See [AGENTS.md](AGENTS.md) for agent guidance. `LLM-helpers/` and `archive/local/`
hold gitignored local automation, logs, and scratch work.
