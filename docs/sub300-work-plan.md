# Sub-300 upper-bound goal and working plan

## Goal

Prove, with a complete checked construction,
`limsup_{n→∞} D(n)/log₂(n) < 300`, where `D(n)` is the minimum depth of a
binary-comparator sorting network on `n` wires.

## Restart here

1. Read [`docs/research-index.md`](research-index.md) for the repository's
   current proof map and active upper-bound routes.
2. Start with the active structural route's
   [`RESEARCH-SEQUENCE.md`](../upper-bound/experiments/direct-multiway/RESEARCH-SEQUENCE.md)
   and [`README.md`](../upper-bound/experiments/direct-multiway/README.md), then
   inspect its source and experiment index. For historical tapered candidate
   estimates, see [`TAPERED-HANDOFF.md`](../upper-bound/experiments/coupled-multiway/TAPERED-HANDOFF.md).
   Handoffs and screens are leads, not proof status. If the active route has
   changed, update this pointer and the index.

## Priorities

- Find a structural algorithm/schedule with a credible priced path below 300;
  distinguish proved facts, finite screens, conditional estimates, and
  conjectures.
- Attack the highest-risk global composition or invariant first. A local
  separator/merge improvement is useful only if its correctness and depth
  compose through an all-depth scheduler and yield the claimed limsup bound.
- Before substantial Lean work, write the proposed invariant and its exact
  transition/terminal obligations, then seek a decisive mathematical or
  computational falsification gate. Use finite screens to reject bad routes,
  never as substitutes for universal proofs.
- Once the route survives, formalize modularly, keep scratch work outside
  promoted packages, and verify the complete asymptotic endpoint and trust
  boundary.

## Working rules

- At each restart, check `git status`, branch, and recent commits; preserve
  useful work with focused commits. Do not overwrite another worktree's files
  or leave long-running processes behind.
- Keep source, handoffs, and generated artifacts separate. Put reproducible
  scripts beside their experiment, summarize large outputs, and index only the
  current result; mark superseded screens clearly.
- Prefer existing `LLM-helpers` indexes and quiet, focused Lean checks. Do not
  rebuild broadly or chase linter noise without need. Do not add axioms,
  `sorry`, or trust extensions.
- Update the relevant handoff/index when a gate changes status. Report the
  strongest proved coefficient, the candidate coefficient and assumptions,
  the single largest open proof gap, and the next decisive action.
- Follow [`AGENTS.md`](../AGENTS.md), especially its trust, worktree, and
  verification rules. Do not push or publish.
