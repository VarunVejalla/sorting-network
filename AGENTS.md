# Project guide

This is a Lean 4 research project on explicit bounds for sorting-network depth.

## Research objective

For `D(n)`, the minimum depth of a sorting network on `n` inputs using binary comparators, refine the bounds on

\[
\liminf_{n\to\infty}\frac{D(n)}{\log n}
\quad\text{and}\quad
\limsup_{n\to\infty}\frac{D(n)}{\log n}.
\]

The checked-in AKS formalization is a research base, not the whole project objective. Work may concern lower bounds, upper-bound constructions, constants, formal verification, or the gap between liminf and limsup. Use a consistent logarithm base when comparing constants and state it explicitly.

The current priority is the upper bound on `limsup D(n)/log_2 n`. Read
[`docs/research-index.md`](docs/research-index.md) first for the current local
proof map and remaining obligations. The September handoff predates substantial
local Paterson work. A new local primitive alone does not improve the final
sorting bound; trace correctness and depth through the global scheduler.

## Shared working rules

- Treat `AGENTS.md` as the canonical instructions for every coding agent. Tool-specific files should point here rather than duplicate policy.
- Inspect the current source and proof before relying on repository notes; the clone and handoff may describe different revisions.
- Keep mathematical status explicit: distinguish kernel-checked results, published results, derived but unaudited arguments, and conjectures or research leads. Never promote a handoff's provisional constants to theorems without a complete proof.
- Preserve the handoff archive. Start with [`AKS_CODEX_HANDOFF_2026-09-27/README_START_HERE.md`](AKS_CODEX_HANDOFF_2026-09-27/README_START_HERE.md), then consult its proof ledger, repo map, current research state, and contribution plan. Prior handoffs are historical context and may contain superseded claims.
- For Lean changes, keep definitions computable when appropriate, state complexity in network depth, and avoid adding axioms, `sorry`, `native_decide`, or trust extensions without clear justification and explicit user agreement. Follow local module conventions and cite the mathematical source of nontrivial constructions.
- Verify only as needed for the requested work. A focused check is usually preferable to an unnecessarily broad build; report exactly what was checked and what was not.
- Keep unrelated changes and generated/build artifacts out of commits. Do not push, publish, or contact others unless explicitly asked.

## Repository map

- `AKS/`: Lean sorting-network, expander, halver, separator, and Seiferas bag-tree formalization.
- `AKS/Bounds/PatersonTight.lean`: complete rounded Paterson bound, all-n coefficient `6991` and limsup coefficient `6990.5`.
- `AKS/Bounds/Paterson.lean`: previous complete Paterson-halver bound with coefficient `10^6`.
- `AKS/Seiferas.lean`: inherited executable MGG-based network and bound.
- `AKS/Paterson/`: the completed rounded bag proof and its allocation, root rebuild, and child invariants.
- `docs/`: mathematical notes and design documents.
- `Random/`, `rust/`, `scripts/`: certificate, experimental, and maintenance code; inspect their local documentation before running expensive workflows.
- `AKS_CODEX_HANDOFF_2026-09-27/`: preserved research handoff and status ledger.

## Tool entry points

- Claude Code: `CLAUDE.md` points to this file.
- Cursor: `.cursor/rules/project.mdc` points to this file.
- Codex and other agents: follow this `AGENTS.md` directly.

Useful starting commands (run from the repository root):

```sh
lake exe cache get
lake build AKS
```

The cache download may require network access. Do not build optional certificate targets unless the task needs them.
