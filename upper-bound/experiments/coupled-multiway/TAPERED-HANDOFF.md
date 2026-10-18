# Tapered-model handoff: what “about 528” means

Status: parameter-model estimates and conditional research leads from
`upper-bound/experiments/tapered/NOTES.md` and `SURVEY.md`, not proved sorting
bounds. The figures below must not be described as kernel-checked endpoints.
This handoff preserves the assumptions for another reviewer or implementer.

## Estimates, ordered by strength and credibility

- **Current verified endpoint: 1419.** The best package proves
  `limsup D(n)/log2(n) <= 1419` using Chvatal's two-round separator and its
  existing schedule.
- **Slack-free candidate: 935 ideal / 1025 with the power-of-two window.**
  This is the more concrete improved candidate at `(k,A,nu)=(64,128,1/64)`
  with `epsB=2^-26`. It depends on eliminating the equal-block schedule drift
  (“slack”) through an inhomogeneous flow table and rewriting the relevant
  flow lemmas. Removing only half the slack predicts 1246; 90% removal predicts
  1084. The related `(64,64,1/16)` sub-1000 candidate prices at 945 but has
  additional actual-schedule obligations.
- **Four-change tapered L4: 650 ideal / about 780 windowed.** Assumptions:
  remove schedule slack; remove top-node condition (4.3); obtain fringe
  fraction near `1/2`; use per-side/adjacent accounting. It still uses the
  existing fringe floor `f>=92160` and `epsB≈2^-20`.
- **The “about 528” model: 528 ideal / about 700 windowed.** It uses the same
  four L4 changes, but also requires proving Property F at the much smaller
  fringe `f≈2^10`, allowing `epsB≈2^-12`. The 528 is an ideal continuous
  depth/slope estimate; integer windows add roughly 170 in this screen. No
  small-fringe Property F theorem or global scheduler proves this candidate.
- **Variant B: 1354.5 ideal** (`3*2709/6`), another hand estimate, not an
  endpoint. Locality-only changes with the old top condition price around
  1250–1290 ideal.

The cited candidate values come from the tapered workstream's exchange-rate
model and exact-rational screens, not a checked global construction. The
currently available scratch proofs establish selected local pieces only:
variable-window and signed-reserve inequalities, address-debt identities,
integer rounding, variable-slot intruder estimates, and portions of ragged
bootstrap geometry/counting. The central missing gates are a schedule-specific
outsider transition, the variable-width induction across stages, a global
scheduler that preserves the signed address profile, and an actual small-fringe
Property F proof for the 528 variant. Passing a local arithmetic lemma does
not supply the sorter or its depth theorem.

## Why 528 is not close to 200

Even granting all four L4 changes and the reduced fringe floor, the windowed
model is around 700. Within this family, the tapered notes judge sub-600
unlikely without separately reducing the power-of-two/integrality window and
the fringe floor. Reaching 200 likely requires a different depth/growth trade:
at the 1.49 bits of growth per L4 stage, a stage would need depth below about
298 instead of the 788-layer screen. This is a structural separator or
schedule improvement, not a small epsilon adjustment.

The best next use of the 528 work is therefore to validate its gates in order:
(1) prove the tiny-fringe Property F contract for the actual two-round
separator; (2) prove the no-slack, per-side interface with signed variable
widths; (3) connect that interface to the real stage scheduler and establish
the all-rank outsider transition; (4) reprice the resulting integer schedule.
If (1) fails at `f≈2^10`, the 650/780 L4 screen is the fallback target. If
either no-slack or top-condition removal fails, the more conservative
935/1025 candidate still merits separate review.

Signature requested by the user: **GPT-6-astra-high**.
