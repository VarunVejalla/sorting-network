# Ticket registry schema

`tickets.json` is the machine-readable source of truth for upper-bound research tickets. The
hand-written README table and the ticket documents are views; `scripts/tickets --table` prints a
current table. Validate with `python3 scripts/tickets` (CI: `.github/workflows/tickets.yml`).

| field | meaning |
|---|---|
| `id` | `UB-NN`, never reused |
| `title` | one-line idea |
| `priority` | `P1` direct route with the current architecture, `P2` architectural change with open composition work, `P3` high-upside exploratory |
| `status` | `proposed` (idea, nothing done) · `ready` (well-posed, can start) · `active` (someone is working; set `owner` or `branch`) · `blocked` (name the blocker in `notes`) · `parked` (paused with resumable state; see `evidence`) · `done` · `rejected` (record why in `ruled-out.md`) |
| `claim_level` | strength of the strongest result so far, matching AGENTS.md: `none` < `conjecture` < `simulation` < `model` (parameter model / scripts) < `hand-proof` (derived, unaudited or certified numerics) < `kernel-checked` (Lean, axiom-clean) |
| `baseline` / `projected` | coefficient before / after the idea if it works (`projected` is never a theorem unless `claim_level` is `kernel-checked` and status `done`) |
| `owner` | agent or person currently responsible (free text), or null |
| `branch` | git branch or worktree holding unmerged work, or null |
| `depends_on` | ticket ids that must finish first |
| `first_deliverable` | the acceptance test of the next step |
| `evidence` | repository paths (checked to exist) |
| `notes` | status details; keep to a few sentences |

Rules (`docs/agent-protocol.md`): an agent starting work sets `status: active` plus `owner` and `branch`
in the same commit that creates its worktree; when it stops it updates `status`, `claim_level` and
`evidence`; negative results go to `ruled-out.md` and the ticket becomes `rejected` or `parked`.
