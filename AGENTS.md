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
- Parallel agents: follow [`docs/agent-protocol.md`](docs/agent-protocol.md) (own worktree per ticket, never leave uncommitted edits in the `main` checkout, claim levels, handoff report, verification checklist). Tickets are in `upper-bound/backlog/tickets.json` (`python3 scripts/tickets`).
- Verifying a claimed upper bound: read [`upper-bound/TRUSTED.md`](upper-bound/TRUSTED.md); run `python3 scripts/check-contribution`. The accepted constant is recorded in `upper-bound/STATUS.json`.

## Working efficiently (indexes, long runs, sub-agents)

Long sessions are dominated by re-reading context, so look things up instead of rediscovering them:

- **Indexes first.** `LLM-helpers/README.md` lists the helpers. Use them in this order:
  - `LLM-helpers/SUB500-MAP.md`: current sub-500 / route (d) state, which outputs are current or
    superseded, script CLIs.
  - `LLM-helpers/LEAN-NOTES.md`: Lean conventions and gotchas, including the Bool and row orientation.
  - `LLM-helpers/AKS-MODULE-MAP.md`: which module.
  - `LLM-helpers/AKS-API-INDEX.md`: exact signatures; grep it, don't read it. Regenerate with
    `python LLM-helpers/lean_api_index.py` after adding or renaming declarations.

  `LLM-helpers/` is gitignored, so from another worktree use the main checkout's copy by path.
- **Keep the indexes current.** When you finish a milestone, update `SUB500-MAP.md` (or the relevant
  map) and `upper-bound/experiments/INDEX.md`. Mark superseded outputs as superseded rather than leaving
  them for the next agent to guess.
- **Long runs.** Run sweeps in the background with output files. Watch them with a monitor that reports
  only completion or failure, at 10–30 minute polls; per-progress events each cost a full-context turn.
  Check status in batches.
- **Sub-agents.** Delegate self-contained work that has a written spec to sub-agents, and keep decisions
  and integration in the main thread. Good fits: independent reviews (a fresh context is the point),
  mechanical ports (for example float evaluators to interval arithmetic), Lean lemmas with a fixed
  statement, and running and tallying covers. Tell the sub-agent which files it may write, and not to
  touch running processes or other branches.
- **Lean edits.** Build one module, grep only the errors, `#print axioms` in a scratch file, and run
  `python scripts/sorry-gate` before pushing (details in `LEAN-NOTES.md`).

## Repository map

- `upper-bound/best/`: current verified upper package, coefficient `789.75` (UB-31: design P with the walk-bound and padded fringe separators, built on the Chvátal two-round modules).
- `upper-bound/alternatives/chvatal-1419/`: previous best (two-round separator, coefficient `1419`).
- `upper-bound/alternatives/chvatal-1770/`: older best (one-round separator, coefficient `1770`).
- `upper-bound/backlog/`: ticket registry (`tickets.json`), research tickets, parked ideas and ideas ruled out (read before proposing a new separator idea).
- `upper-bound/contributions/`: submission package for a proved better constant (pinned statement, guards); `upper-bound/TRUSTED.md` explains what is trusted.
- `upper-bound/experiments/INDEX.md`: lifecycle state of every experiment folder.
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
