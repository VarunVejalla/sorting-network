# UB-42 status

2026-10-20. Codex (GPT-6), branch `sub300-structural`, isolated worktree
`.claude/worktrees/sub300`, based on main `5f03290`.

Active bounded paper test. No improved coefficient or Lean theorem.
Reuses UB-24's identities and the existing integer D2 flow; no new routing
Lean was written. Read PLAN and REVIEW for the precise oracle relaxation.

Observed results, all (x,y,z)=(2,3,2), native policy, seed0:

| d | exact cutoff C | epsB | epsF | deltaF | root | prefix dominance | result |
|---|---:|---|---|---|---|---|---|
| 8 | 1024 | 0 | 1/16 | 1/8 | exact | no | exact final counts at q/N=1/2,1/3,1/16 |
| 9 | 1024 | 1/100 | 1/16 | 1/8 | exact | no | L1=16 at q/N=1/2 |
| 9 | 1024 | 1/100 | 1/16 | 1/8 | exact | yes | L1=66 at q/N=1/3 |
| 9 | 1024 | 1/100 | 1/16 | 1 | exact | yes | L1=2 at q/N=1/3 and1/16 |
| 10 | 1024 | 1/1000 | 1/16 | 1/8 | exact | yes | sampled1/2,1/3,1/16 pass |
| 10 | 1024 | 3/1000 | 1/16 | 1/8 | exact | yes | L1=46,12 at1/3,1/16 |
| 10 | 1024 | 1/128 | 1/16 | 1/8 | exact | yes | L1=236,100 at1/3,1/16 |
| 11 | 65536 | 1/100 | 1/16 | 1/8 | exact | yes | sampled1/3,1/16 pass |
| 11 | 65536 | 1/100 | 1/2 | 1/16 | exact | yes | sampled1/3,1/16 pass |
| 12 | 65536 | 1/100 | 1/16 | 1/8 | exact | yes | L1=4324,19 wrong final bags at1/3 |
| 12 | 65536 | 9/1000 | 1/16 | 1/8 | exact | yes | L1=3802,18 wrong final bags at1/3 |

The larger cutoff matters: its exact-sort depth is136, still below a
hypothetical234-layer ordinary stage. Thus the C1024 failures did not reject
this larger frontier. The d12 failure now shows that simply increasing the
cutoff to65536 does not close the tested coarse contract either.

For this geometry the leading stage rate is5/4. The nominal q12 three-sort
cost would be234, coefficient292.5, before a valid invariant and provider.
The existing bulk walk table gives approximately0.00935 at q12. There is no
certified fringe provider within that budget; fitting a low-J fringe estimate
is not a construction. Large clipped top bags cannot be charged as small
exact frontiers. The exact initial root is also unpriced.

Recorded witnesses are small lists of nonideal decisions; all other nodes
are ideal. Replay does not call the LP, and verifies local integer bounds,
capacity/zero conservation, final native partition and, where enabled,
every input prefix. It shares code with the oracle, so is not independent
verification. Example:

    python upper-bound/experiments/prefix-flux/replay.py upper-bound/experiments/prefix-flux/monotone-witness.json

The surviving path now has a scaling capacity obstruction:678 wrong ones
enter a wholly-zero native subtree with total future escape at most8192/15.
See CUT-OBSTRUCTION. Raising any fixed cutoff only shifts the same coarse
oracle failure to a larger scale. The9/1000 witness also lies below the
q12 bulk-table value; neither statement supplies a universal provider result.

Verification: exact replay of both d12 witnesses and the d9 monotone witness;
`cut_certificate.py`; ticket validator and git diff check. The existing table
builder now avoids allocating never-active leaves and accepts a finite
horizon. Full old/new tables matched for d3..7, designs U/D2/P (15 cases).
No Lean build or contribution validation: no claimed sorting bound.

Next: derive a capacity-compatible rank-sensitive spill contract for an actual
fixed provider, using the existing tail work first. Do not formalize the current
coarse postcondition interface or infer impossibility for all fixed providers.

## Moderate-tail follow-up

MODERATE-TAIL now derives a reviewed rank-sensitive tail and a centered-ragged
layout avoiding a large padding surcharge. Numerical interval checks at fixed
dyadic witnesses give escape bounds530 and132 at the coarse trace's critical
t4/t5 bags, excluding its1099 and678 choices. The global recurrence and
tiny-rank guarantee remain open; no improved coefficient is claimed.

The oracle's Boolean words now use run-length encoding. Prefix dominance is
checked at all input/output run endpoints, which suffices between endpoints
because the difference is linear. Existing saved traces still replay with
the same decisions and final errors; no arrays proportional to N are needed
for the prefix check.

Source audit identified the next essential gate: the current implementation
interleaves incoming wires in static global-label order. The concatenation
oracle does not model that stronger reachability. See ORDERED-GATE before
doing further recurrence tests. In the faithful ordered model an exact root
must leave no later errors, a useful diagnostic missing from the old harness.
The historical default capacity probe is a concatenation relaxation;
the ordered follow-up below models the actual interleaving.

## Ordered gate and local price follow-up

Ordered static-label mode is now implemented and independently reviewed;
see ORDERED-GATE for controls and limitations. It checks the sorted-root
fixed point and global Hamming nonincrease, and allows errors inside a
threshold-straddling output port. Tests remain adversary samples.

TINY-FRINGE records a reviewed interval-bound refinement retaining the exact
first integer support cap. A thirteen-row point is possible in the paper
bounds only at a very small supported rank fraction. It fails the current
Lean hf16 API guard; the reviewed zero/nonzero-jmax extension and numerical
proof are not formalized. It is not the stronger fringe assumption used in
the current ordered samples.

INFLATED-SCHEDULE records a reviewed constant inflation of the D2 table,
giving exact4096-row rectangles and a large fixed final cleanup charged once.
This removes the repeated small-sort/padding obstruction, not the global
invariant. Next: ordered spill/profile recurrence and universal D2 fringe
ratio/native partition; no Lean until the complete paper gate closes.
