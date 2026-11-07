# Chvátal improvement experiments

`scripts/chvatal_param_search.py` explores parameter constraints; it is not a
proof of an improved sorting coefficient. The prior local edits to that script
were preserved during relocation.

UB-09 ideal-limit screen (2026-11-02, model): `UB-09-IDEAL-LIMIT.md`,
`scripts/ideal_limit_screen.py`, `scripts/fringe_attack_scan.py`. With attack-level
separators the tree bottoms out at about 300; a sharper tree analysis is the
remaining lever.

Tree pricing (2026-11-03, model): `TREE-PRICING.md`, `scripts/tree_pricing.py`,
`scripts/centred_pricing.py`. It corrects UB-09 (separator stage of three sorts). No existing
tree analysis gets below about 380 even at attack-level separators. Sub-300 needs a cheaper
separator stage at the same leak.

Stage screen (2026-11-03, model + attack sims): `STAGE-SCREEN.md`, `scripts/stage_screen.py`,
`three_round_sim.py`, `round1_tail_attack.py`. No column-sort / random-scramble stage reaches 300.
The best is band + merge-first at about 333 (attack, R2c). The binding quantity is the round-1 tail,
which decays like 1/W under attack.

Designed scrambles (2026-11-07, hand + attack sims): `DESIGNED-SCRAMBLE.md`,
`scripts/designed_scramble_screen.py`. The 1/W tail (about 0.16/W) holds for every scramble
design with n >= m columns by a design-independent random-target bound. Designs help only at small
nodes (m > n). The light-tail lever is dead, and sub-300 is out of reach in this architecture at
model level.

Keep scratch Lean in an independent package here or in gitignored local helpers,
never inside `../../best` until promotion. Relevant current notes are in
`../../../docs/chvatal-two-round-small-ranks.md` and
`../../../docs/chvatal-fringe-obstruction.md`.
