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
invariant. The `(3,3,2)` fringe-factor note gives an exact two-step allocation
identity: under `g,rho <= 1/256`, ordinary sender ratios are at most `9/8`.
The new `d2_fringe_audit.py` checks the narrowed schedule cases and all these
rational inequalities through depth 100; it found no finite counterexample.
The all-depth `g` induction and floor/parity schedule lemmas remain open. See
[D2-FRINGE-FACTOR.md](D2-FRINGE-FACTOR.md). Next: ordered
spill/profile recurrence and universal D2 native partition; no Lean until the
complete paper gate closes. Important transfer gap: the 8192-row fringe ratio
does not meet existing `NodeGeom`/`TwoRoundSeparatorExists` requirements
(`m>2^42`, `f=0` or even `f>=131040`, with exact divisibility equations), so a
new small-row provider and exact geometry are required.

## Exact compressed flow and first-sort profile gate

Current next-step specification: **PROFILE-GATE.md**. It records a freshly
reviewed stronger local interface for the actual three-sort construction:
prefix dominance over its mandatory first column sort, and shifted sparse
tails above every baseline row. The shared-witness counting overhead is
explicit, including reflected cut coordinates. Global preservation remains
unproved. Reviews: `first_column_review`, `shifted_profile_audit` (GPT-6-luna).

`flow_dag.py` shares identical deficit subtrees instead of enumerating4^d
bags. Reproducible comparison against the existing explicit table matches
17541 active rows at d3..10. At d40 it represents the complete88-stage flow
in29483 states and checks terminal native intervals for every reachable type.
Finite checks through d80 find minimum ordinary fringe ratio1/303, attained
already at d20,t22,level6,a2121,pi14; this is NOT an all-depth geometry proof.

`sparse_probe.py` retains actual wrong-label intervals and tries to preserve
the incoming word whenever its contract allows, rather than sorting every
large output port incidentally. Full d20 tests expose ordered capacity gaps
for remote root errors if the mandatory first sort is omitted; including it
excludes the three sampled gaps. Central and column-aligned initial profiles
also pass the full schedule. See PROFILE-GATE for scope and parameters.
These samples retain the unpriced fringe/bulk assumptions: no sorting bound.

Useful focused commands:

    python upper-bound/experiments/prefix-flux/flow_dag.py --depth 20 --compare-explicit 10
    python upper-bound/experiments/prefix-flux/first_column.py
    python upper-bound/experiments/prefix-flux/sparse_probe.py --horizon 60 --initial outer

The rectangle-to-port frame is checked against `R1Wire`/`R1Exec` and
`PhysicalPack2`: ports are static-order rank intervals, local networks are
presented in that rank order, and physical/semantic whole-row counts agree.
The remaining issue is global transfer, not the rectangular port frame.
`wire_partition_check.py` now checks the stronger discrete routing identity:
each active node's up/down rank slices, plus unchanged inactive bags, partition
every next-stage bag's exact static-wire intervals with neither omissions nor
duplicates. It passed all stages at depths 2--8 for scale 1 and 2 (699,048
bag checks per scale at depth 8). This validates the flow-coordinate mapping
for a later profile model; it adds no comparator constraint or global invariant.
`PROFILE-GATE.md` now gives the exact global defect decomposition into a
cross-bag alignment term plus local prefix defects, and its one-stage bound
when local rank tails are available. `global_prefix_flux.py` checks the
decomposition at every global cut and stage for random Boolean profiles,
including depth 8 at scale 1. This validates the algebra and partition
coordinates only; it does not establish the needed quantitative contraction.
The follow-up finite-cut closure remains modest: depth8/scale4096 uses at
most2,625 local cuts per stage. The ordered `coupled_rank_lp.py` now imposes
global-profile consistency and local prefix dominance at those selected cuts.
At depth6/scale4096, even with root rank-tail bounds and the exact first-column
lower bound at all 4096 full-row cuts, an integral relaxation witness leaves
456,448 wrong keys outside the crossing terminal block. This is not a network
counterexample because unselected local prefixes remain unconstrained; it
shows the finite interface still cannot certify the candidate. See
`PROFILE-GATE.md` for the exact cut counts, witness scope, and next gap.
`rank_recurrence.py` propagates zero-count intervals using the local
one-sided rank-tail bounds, including the required common-witness factor
`m^2` for baselines. At depth7, scale65536 and threshold1/3 it cannot certify
63 terminal blocks as pure. This is a conservative-relaxation failure from
lost correlations, not a counterexample to a fixed core. See PROFILE-GATE for
the exact conditional frame argument and next invariant requirement.

`coupled_rank_lp.py` keeps each node's output prefix profile correlated with
all of its ports and solves one global LP over the D2 horizon. Even with an
exact sorted root, its corrected tail-only contract admits an integral
terminal impurity at d6 (7,884,863 wrong keys total, maximum1,904,413 in one
block). The missing constraint is prefix dominance over the actual local
input profile. The ordered sparse oracle does impose that for selected
input-dependent traces: d12, scale65536, threshold1/3, root-error fraction
10^-6, outer/left/right band profiles all pass with1782 errors confined to
the crossing block. No fixed provider or arbitrary-input root initialization
has been established. See PROFILE-GATE for full scope and commands.

The LP now stores its path constraints sparsely; recoloring and interval
queries avoid repeated scans. First-sort validation:8490 literal comparisons;
recoloring/interval validation:3000 randomized exact comparisons. Historical
monotone trace replay remains valid. No Lean build was needed or run.

The joint profile-weighted MGF screen is recorded in `PROFILE-WEIGHTED-MGF.md`
and implemented in `profile_mgf_dp.py`. The finite nested-subset DP agrees
with direct profile enumeration on a small instance. Its asymptotic variational
rate suggests a possible local-tail gain, but the current tangent calculation
is only a floating diagnostic and is not a certified upper bound. Even a
certified local gain would leave the coupled global transfer and terminal
purity gap open; no coefficient improvement or Lean result follows.
