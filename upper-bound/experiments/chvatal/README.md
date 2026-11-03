# Chvátal improvement experiments

`scripts/chvatal_param_search.py` explores parameter constraints; it is not a
proof of an improved sorting coefficient. The prior local edits to that script
were preserved during relocation.

UB-09 ideal-limit screen (2026-11-02, model): `UB-09-IDEAL-LIMIT.md`,
`scripts/ideal_limit_screen.py`, `scripts/fringe_attack_scan.py`. With attack-level
separators the tree bottoms out at about 300; a sharper tree analysis is the
remaining lever.

Keep scratch Lean in an independent package here or in gitignored local helpers,
never inside `../../best` until promotion. Relevant current notes are in
`../../../docs/chvatal-two-round-small-ranks.md` and
`../../../docs/chvatal-fringe-obstruction.md`.
