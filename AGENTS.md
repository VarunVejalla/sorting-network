# Project guide

This is a Lean 4 research project on explicit bounds for sorting-network depth.

## Research objective

For `D(n)`, the minimum depth of a sorting network on `n` inputs using binary comparators, refine the bounds on

\[
\liminf_{n\to\infty}\frac{D(n)}{\log n}
\quad\text{and}\quad
\limsup_{n\to\infty}\frac{D(n)}{\log n}.
\]

The formalizations are a research base, not the whole project objective. Work may concern lower bounds, upper-bound constructions, constants, formal verification, or the gap between liminf and limsup. Use base-two logarithms when comparing the displayed constants.

The current priority is the upper bound on `limsup D(n)/log_2 n`. Read
[`docs/research-index.md`](docs/research-index.md) first for the current local
proof map and remaining obligations. The September handoff predates substantial
local Paterson work. A new local primitive alone does not improve the final
sorting bound; trace correctness and depth through the global scheduler.

## Shared working rules

- Treat `AGENTS.md` as the canonical instructions for every coding agent. Tool-specific files should point here rather than duplicate policy.
- Inspect the current source and proof before relying on repository notes; the clone and handoff may describe different revisions.
- Keep mathematical status explicit: distinguish kernel-checked results, published results, derived but unaudited arguments, and conjectures or research leads. Never promote a handoff's provisional constants to theorems without a complete proof.
- Historical handoffs are preserved under `archive/handoffs/`. Consult them only for historical context; start current work with `docs/research-index.md` and the relevant package README.
- For Lean changes, keep definitions computable when appropriate, state complexity in network depth, and avoid adding axioms, `sorry`, `native_decide`, or trust extensions without clear justification and explicit user agreement. Follow local module conventions and cite the mathematical source of nontrivial constructions.
- Verify only as needed for the requested work. A focused check is usually preferable to an unnecessarily broad build; report exactly what was checked and what was not.
- Keep unrelated changes and generated/build artifacts out of commits. Do not push, publish, or contact others unless explicitly asked.

## Repository map

- `upper-bound/best/`: current verified Chvátal upper package, coefficient `1770`.
- `upper-bound/experiments/`: separate improvement attempts; expander certificate tooling is optional.
- `upper-bound/alternatives/legacy/`: rounded Paterson all-n coefficient `6991`, limsup `6990.5`, and older Seiferas/MGG constructions.
- `lower-bound/best/`: complete Kahale lower-bound endpoint and its foundations.
- `lower-bound/experiments/`: retained lower-bound research beyond that endpoint.
- `research/limit-existence/`: conditional limit and amplification/repair research.
- `docs/`: mathematical notes and design documents.
- `scripts/`: repository maintenance; experimental scripts live with their workstreams.
- `archive/`: historical scaffolding and handoffs. `archive/local/` is gitignored.
- `LLM-helpers/`: gitignored generic local helpers, logs, and scratch proofs.

Keep scratch Lean outside `best` packages until explicitly promoted. Each proof
package has its own Lake environment. The upper best and legacy packages use
overlapping AKS module names for separate network models; build them separately.
The lower and limit packages deliberately depend on the legacy package and
share its foundations. Compare definitions before transferring lemmas between
the upper best model and legacy model.
All packages share root `.lake/packages`; avoid `lake clean`, which can remove
shared dependency artifacts. Use quiet logs in `LLM-helpers` for long checks.

## Tool entry points

- Claude Code: `CLAUDE.md` points to this file.
- Cursor: `.cursor/rules/project.mdc` points to this file.
- Codex and other agents: follow this `AGENTS.md` directly.

Useful starting commands (run from the repository root):

```sh
lake exe cache get
cd upper-bound/best
lake build
lake build AKS.Bounds.Chvatal1830Axioms
```

The cache download may require network access. Do not build optional certificate targets unless the task needs them.
