# Sub-300 agent guide

## Goal

Prove, with a complete kernel-checked argument,

```text
limsup D(n) / log2(n) < 300,
```

for sorting networks on `n` wires. The accepted bound remains 789.75; the D2
candidate and its local coefficient 230 are not a global theorem.

## Resume efficiently

1. Read `AGENTS.md`, then `docs/sub300-work-plan.md` for the current priorities.
2. Start with `upper-bound/experiments/prefix-flux/HANDOFF.md`; consult its
   README for source locations. Treat the handoff as current status and older
   search/status logs as historical unless verified against current source.
3. Work on branch `sub300-structural` in `.claude/worktrees/sub300`. Keep
   generated builds and experiment outputs under ignored `LLM-helpers`.
4. Identify the smallest decisive proof gate before editing. Do not repeat
   already closed gates or extend Lean bridges before the schedule-level
   transition is understood.
5. Keep claims scoped: distinguish a checked local lemma, a conditional
   interface, a model/screen, and the all-size theorem. A fixed-core bound or
   abstract flow invariant alone does not improve the limsup bound.
6. For Lean work, build only the affected source/dependencies with the focused
   checker described in the prefix-flux README. Report exactly what passed;
   caches are not proof evidence.
7. Keep source notes and generated artifacts separate. Update the handoff and
   relevant index when a proof gate closes or fails; mark superseded material.
8. Commit coherent source-and-handoff milestones. Do not commit generated
   artifacts, alter the accepted package, or claim success until the complete
   contribution checks pass.

## Current critical gate

The D2 abstract affine-flow invariant and local physical-core transfer are
checked, but the proof still lacks the exact all-stage transition for the
actual schedule: physical tile profiles and false masses must produce the
abstract port counts and receiver tags, including ragged/startup/exceptional
roles. The handoff's **Next proof gate** section names the smallest current
step. If that transition closes, continue with a spatial/distance-sensitive
terminal invariant, fixed cleanup, and depth/padding accounting. Reassess the
route if the transition is false or does not support a terminal bound.
