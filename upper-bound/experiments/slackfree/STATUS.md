# Status of the slack-free flow-table project (paused 2026-10-11)

**Paused by decision**, not by failure: another effort targets a much better bound (≈945), so this
route (modeled ≈1261 at the certified window) was stopped after Stage 1b step 1. Everything below is
committed on branch `worktree-runaware` and can be resumed.

## Where it stands

| stage | content | status |
|---|---|---|
| analysis | `../tapered/` (model: slack is 48% of the (4.2) budget; larger ε alone does not help), `SLACKFREE.md` (derivation: (6,7,6) does not close; same invariant P gives ≈1261 at (6,10,6); new invariant Q ≈1104), `INTERFACE.md` (interface, staged plan, 5–8k line estimate) | done |
| Stage 0 gate | `GATE0.md`, `d2lean.py`, `invariant.py`, `schedule.py` (+ `.out`): frozen rounded D2 rule (π′ = π₀ + ((a−π₀) mod Γ), Γ = c(i+1,t+1)/2^39), finite-role invariant (39 classes at (6,10,6)), (4.2) margin 2.1356, schedule tf=(8d+κ)/3 with period 6 in d, headline D(n) ≤ (3784/3)·lg n − 24433 | **GO** |
| Stage 1a | `../slackfree-lean/` (copy of the 1419 package): `FlowTableB`, `FlowFacts`, `uniformB`, `flowFacts_current`, `downSetB` | done, green, headline still 1419 |
| Stage 1b-1 | `wireSets`/`execPlacement`/`X`/`bad_send0_real`/`fringe_send_real`/`stagesNet` generic over `FlowTableB`; `NodeSpecB` (additive) | done, green (commit `177169a`) |
| Stage 1b-2 | per-child windows (`NodeSpecB.intruder_keys`), per-child `bad_send0_real`, deficit-form Lemma 4.1, generic `RealSpecs/BadSendField/FringeSendField` over `FlowFacts` | **not started** (agent hit a session limit before editing; the tree is clean at `177169a`) |
| Stage 2 | D2 table at today's (6,12,6) constants (headline still 1419), replacing `NodeShape` by the role-class invariant | not started |
| Stage 3 | (6,10,6) schedule, constants, depth, headline ≈ 1261.33·lg n − 24433 | not started |

## To resume
1. `cd upper-bound/experiments/slackfree-lean` (builds green: `lake build`, `lake build AKS.Bounds.Chvatal1830Axioms`;
   `packagesDir` is `../../../.lake/packages`, needs the worktree `.lake` junction or a root `.lake`).
2. Continue with the 1b-2 prompt in `INTERFACE.md` §4 / the recommendation list below, then Stage 2, Stage 3.
3. Recommended 1b-2 order (from the 1b-1 hand-back): `NodeSpecB.intruder_keys` (windows
   `[π/2 + off j, π/2 + off (j+1))`, hypotheses `off 0 = 0`, `Monotone off`, `a = π + off 64`); per-child
   `window_real`/`bad_send0_real`/`fringe_send_real` with `τ_j = F.down t q j`; generalize `hM` to
   child-j native count ≤ `down j + ρ_j` via `theta`/`residAt`; generic `RealSpecs`/`BadSendField` taking
   `FlowFacts` as a hypothesis, instantiated at `uniformB` by `flowFacts_current`.

## Known caveats (from the Stage 0 gate)
* The two wire-count identities and the rounding-grain divisibility are hand-derived; data agree (d ≤ 60 for tables,
  d ≤ 300 for the schedule) but nothing is machine-proved yet.
* Real cost is ≈5–8k Lean lines (centre ≈6k); no slope gain until Stage 3.
* Geometry window: a/c reaches 1.000032, so use `n = 2^(⌈lg a⌉−43)` (c/2^43 if a ≤ c, c/2^42 if c < a ≤ 2c);
  fringes > 8.5e9 occur at (6,10,6) bottom nodes (the Lean `TwoRoundProof` already splits at f < 8.5e9).
