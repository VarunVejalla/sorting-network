# Experiments index

One row per directory in `upper-bound/experiments/`, with its lifecycle state. Keep this file current when
a folder is created, paused, promoted or retired (agent protocol: [`docs/agent-protocol.md`](../../docs/agent-protocol.md)).
Tickets live in [`../backlog/tickets.json`](../backlog/tickets.json) (`python3 scripts/tickets --list`).

Lifecycle: **active** (someone is working; the ticket names owner/branch) · **parked** (paused, resumable; a status
file says how) · **promoted** (merged into `../best`; the folder was removed) · **reference** (finished analysis kept for
its numbers) · **retired** (superseded; kept in history only).

| directory | kind | state | ticket | what it is |
|---|---|---|---|---|
| `chvatal/` | scripts | reference | UB-05 | `chvatal_param_search.py`: parameter-feasibility model for Chvátal's network (slope over k, A, ν, window L) |
| `tapered/` | notes + scripts + Lean | active (Codex, worktree `tapered-945`) | UB-07, UB-23, UB-24 | UB-23 closes initialized shape-specific ownership/count routing. UB-24 proves actual threshold recurrence and cohort conservation; exact native subtree balance at retirement needs coordinated rounding. See `tapered/UB-24-RANK-PROFILE.md`. Provider realization and the global rank invariant remain open; no global sub-1000 theorem. |
| `slackfree/` | notes + exact-integer scripts | parked | UB-12 | slack-free non-uniform flow table: derivation, Stage-0 gate (GO), interface and staged plan; `STATUS.md` says how to resume. The Lean fork (`slackfree-lean`, Stage 1a/1b-1, headline unchanged) lives on branch `worktree-runaware` (commit `177169a`) |
| `runaware/` | Lean package (fork of the former 1770 package) + notes | parked | UB-13 | run-aware first column sort: proved block-merge sorter, 2^29 divisibility, `GenNetwork` stage composition; `DESIGN.md`, `ROADMAP.md`. Payoff shrinks to ~3% at the two-round window |
| `fringe-single-round/` | notes + scripts | reference | UB-15 | reconstruction of the one-round fringe proof's constants and the necessary condition `f ≥ 4.3e7` |
| `direct-multiway/` | Lean + audits | active (another agent) | UB-11 | direct multiway partitioner / profile scheduler |
| `ajtai-multiway/` | scripts + notes | active (another agent) | UB-08, UB-11 | AKS 1992 multiway-halver screens and below-200 plan |
| `k-sorting-2024/` | literature screen | reference | UB-08 | 2024 high-arity k-sorting paper relevance screen |
| `global-cost-audit/` | notes + scripts | active (another agent) | UB-11 | cost audit and research decisions for the global schedule |
| `paterson/` | notes + scripts | reference | UB-06 | audit of the completed Paterson construction (requirements versus cost) |
| `expanders/` | separate Lake package | reference | UB-06 | optional expander-certificate package (own trust boundary) |

## Policy for Lean forks

A fork of the whole best package is ≈190 MB with its build cache and every committed copy stays in history. Therefore:

1. Develop a Lean fork on its **own branch/worktree** (`git worktree add .claude/worktrees/<ticket> -b <ticket>`), not as a
   directory committed to `main`.
2. Commit to `main` only the **notes, scripts and small deltas** (`experiments/<name>/` with a `STATUS.md`).
3. Record the branch and last good commit in the ticket (`branch` field) and in the folder's `STATUS.md`.
4. A fork that is finished is promoted (copy tracked files into `../best`, move the old best to `../alternatives`,
   follow `../TRUSTED.md`) and then removed from `main`.
