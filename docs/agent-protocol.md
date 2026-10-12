# Agent protocol

How parallel agents and people work on this repository without colliding, and how results are accepted.
`AGENTS.md` is the canonical short instruction file; this document is the operating procedure behind it.

## Roles

* **Coordinator** (a person, or the lead agent): owns `main`, the ticket registry, merges and promotion.
* **Worker agents**: each works on exactly one ticket in its own worktree/branch and reports back.
* **Reviewer** (independent of the worker): re-verifies a worker's claims before they are recorded.

## Rules of the shared checkout

1. **Never leave uncommitted edits in the `main` checkout** and never let two agents edit the same file there.
   `main` is the integration point, not a scratchpad. (Observed failure: a merge into `main` collided with another
   session's uncommitted README edits and had to be done by stashing and restoring them.)
2. A worker starts with `git worktree add .claude/worktrees/<ticket> -b <ticket> main` and writes only inside it.
   Build caches are shared through a `.lake` junction at the worktree root (`mklink /J .lake ..\..\..\.lake` on Windows;
   `ln -s` elsewhere); never `lake clean` (it removes shared dependency artifacts).
3. Scratch Lean stays outside `upper-bound/best` until promoted. Whole-package forks live on their branch, not on
   `main` (see `upper-bound/experiments/INDEX.md`, "Policy for Lean forks").
4. Only the coordinator pushes to `origin/main`; nobody pushes without being asked (AGENTS.md).

## Ticket lifecycle (`upper-bound/backlog/tickets.json`, schema in `tickets.schema.md`)

`proposed → ready → active → (blocked | parked | done | rejected)`.

* Taking a ticket: set `status: active`, `owner`, `branch` in the same commit that creates the worktree.
* Pausing: set `parked`, write `experiments/<name>/STATUS.md` (what is done, what remains, how to resume, last good commit).
* Finishing: `done` with `claim_level` and `evidence`; negative results go to `upper-bound/backlog/ruled-out.md` and the
  ticket becomes `rejected` (or `parked` if conditionally dead).
* Validate with `python3 scripts/tickets` (CI: `tickets.yml`). Print the table with `--table`.

## Claim levels (never promote a level without its evidence)

`none` < `conjecture` < `simulation` < `model` (parameter model/scripts) < `hand-proof` (derived, unaudited, or with certified
numerics) < `kernel-checked` (Lean, axiom-clean). A projected coefficient is a **model** until a Lean theorem exists. State
the level in every report and ticket update.

## Handoff report (every worker's final message)

1. Ticket id, branch/worktree, final commit.
2. Result in one paragraph, with its claim level.
3. Exactly what was checked and how (commands, jobs, axioms) and what was **not** checked.
4. Files changed, new theorem statements verbatim (for Lean), numbers with their source (script + output file).
5. Open problems / risks, and the recommended next step.

## Verification checklist for Lean results (reviewer, independent of the worker)

1. Rebuild from the branch (`lake build`, then the package guard such as `AKS.Bounds.Chvatal1830Axioms`); for a promoted
   package delete `.lake/build` first.
2. `#print axioms` on each headline theorem: only `propext`, `Classical.choice`, `Quot.sound`.
3. `grep -rnw "sorry\|native_decide\|admit\|axiom\|unsafe" AKS` is empty (and `scripts/sorry-gate`).
4. Diff the trusted definitions against `main` ignoring line endings (`scripts/trusted-fingerprint --check`).
5. Read the headline statement: no hypotheses, right constant, right quantifiers; check non-vacuity of new definitions
   used in hypotheses.
6. For a claimed improvement: `python3 scripts/check-contribution` (and, once available, the comparator workflow).

## Promotion to `upper-bound/best`

Only after the checklist above and a from-scratch build: copy the tracked files into `best/`, move the previous best to
`alternatives/`, update `Best.lean` + `STATUS.json`, `python3 scripts/trusted-fingerprint --update` (review the diff),
`python3 scripts/check-status`, update READMEs from `STATUS.json`, merge to `main`, record in the ticket.

## Background sessions

Background (non-interactive) sessions may be blocked from writing to the shared checkout: they must work in a worktree.
Rate-limited agents leave state in their worktree: resume them (`SendMessage`) instead of restarting, and ask for an
interim note early so nothing is lost.
