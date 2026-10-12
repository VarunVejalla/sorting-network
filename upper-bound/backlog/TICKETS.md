# Ticket table (generated)

Generated from [`tickets.json`](tickets.json) by `python3 scripts/tickets --table`; edit the JSON, not this file.
Schema and rules: [`tickets.schema.md`](tickets.schema.md), [`docs/agent-protocol.md`](../../docs/agent-protocol.md). The hand-written
[`README.md`](README.md) and the ticket documents remain the narrative; `claim` is the strength of the strongest result so far.

| ID | Priority | Status | Claim | Baseline -> projected | Idea |
|---|---|---|---|---|---|
| UB-00 | P1 | done | kernel-checked |  | Global certificate API and contribution package |
| UB-01 | P1 | ready | none |  | Abstract the local column-sorter interface and identify the exact reusable laws |
| UB-02 | P1 | proposed | none |  | Search for a shallower full sorter at ordinary-node widths |
| UB-03 | P1 | active | hand-proof | 1419 -> 1354.5 | Reduce the ordinary-node height using stronger/tighter separator estimates |
| UB-04 | P2 | proposed | none |  | Replace full column sorts with partial sorting / halving primitives |
| UB-05 | P2 | proposed | model |  | Jointly optimize branching factor, number of rounds, and node geometry |
| UB-06 | P2 | proposed | none |  | Improve expander/halver primitives and compose them with the current node contract |
| UB-07 | P3 | parked | model | 1419 -> 780 | Tapered stranger invariant allowing larger local error |
| UB-08 | P1 | proposed | none |  | Compile the 2024 shallow high-arity k-sorters into binary sorters |
| UB-09 | P1 | proposed | none |  | Extract finite-M constants from Chvatal's M-sorter construction |
| UB-10 | P3 | proposed | conjecture |  | Recover the reported private sub-100 AKS construction |
| UB-11 | P1 | active | hand-proof |  | Price cumulative boundary displacement in the profile scheduler |
| UB-12 | P2 | parked | model | 1419 -> 1261.3 | Slack-free non-uniform flow table (design D2, same invariant P) |
| UB-13 | P3 | parked | model | 1419 -> 1370 | Run-aware first column sort (skip merge levels using sorted input runs) |
| UB-14 | P1 | proposed | simulation | 1419 -> 1050 | Cheap approximate last sort (d-sorter for the third column sort) |
| UB-15 | P1 | proposed | hand-proof |  | Reduce the fringe floor (f below 2^17) for the two-round node |
| UB-16 | P1 | done | kernel-checked |  | Verification hardening of the contribution pipeline |

