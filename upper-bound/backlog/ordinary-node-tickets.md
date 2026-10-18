# Ordinary-node depth tickets

These tickets expand the leading ideas in the [backlog index](README.md). Current baseline details are in
[`docs/upper-bound-1419-cost-audit.md`](../../docs/upper-bound-1419-cost-audit.md) and the checked Lean
interfaces under `../best/AKS/Chvatal/`.

## UB-01 — Abstract the local column-sorter interface

**Priority:** P1 · **Status:** ready · **Scope:** proof engineering enabling sorter experiments.

The two-round pack sorts each of the `n` columns independently at three points. The correctness proof
needs the column network to sort, preserve the multiset of values, operate within its column, and fix an
already sorted column. The depth theorem needs a uniform depth bound. Extract these laws from the current
bitonic-specific `columnSortNetwork` and show the existing bitonic implementation satisfies the interface.

**Acceptance:** the current 1419 theorem still builds through the abstract interface, with no change to
separator statements or endpoint. A new candidate sorter can then be substituted by proving only the
interface and its depth bound.

## UB-02 — Find a shallower full sorter at ordinary-node widths

**Priority:** P1 · **Status:** research · **Scope:** local repeated cost.

At ordinary nodes, bitonic depth is at most 946 for `m <= 2^43`, and the pack runs three such sorts.
Under the current three ordinary stages per six binary logarithms, a uniform sorter depth `S` gives
coefficient `S/2`. Thus `S < 800` is the direct threshold for a coefficient below 1200 without changing
the scheduler. Compare recursive constructions, depth-optimized finite networks, and hybrid merge/sort
families over the full node range, not only at a single input size.

Small base networks are worth measuring, but report their effect on the full recursive depth: fewer
comparators alone do not improve this project's depth bound. At power-of-two sizes, standard Batcher
odd-even merging does not automatically improve on bitonic depth.

**Acceptance:** either a uniformly specified family with a proved depth bound below 800 in the needed
range, or a quantitative screen showing the explored families cannot meet that target. A family need not
have an efficient executable generator if the mathematical object and its depth/correctness are explicit,
but formal construction and verification complexity should be recorded.

## UB-03 — Reduce the ordinary-node height

**Priority:** P1 · **Status:** in progress · **Scope:** separator analysis and geometry.

The formal two-round endpoint currently uses `2^42 < m <= 2^43` and gives coefficient 1419. Hand proof
and exact-rational checks in `../best/notes/two-round/BULK2.md` suggest two-tail Variant B could support
`m >= 2^41`; with a shifted node window this projects to 1354.5. That is not enough for the current
below-1200 target, but it is a useful milestone and a test of the analysis pipeline.

Investigate stronger exact-mass tails, tighter state counting, and alternative separator parameters to
reach a window ending near `2^39` or below while retaining a cost-effective number of sorts. Track the
shared fringe event and global node geometry at every proposed threshold.

**Acceptance:** a certified threshold and complete shared bulk/fringe existence argument, followed by
the shifted geometry and scheduler depth theorem. Keep hand-derived constants separate from proved ones.

## UB-04 — Avoid fully sorting every column

**Priority:** P2 · **Status:** research · **Scope:** change the local invariant.

Current intermediate states are represented by monotone column heights, which is why each stage fully
sorts columns. Determine whether the next round needs full monotonicity or only a weaker property, such as
a rank-sensitive halver guarantee or bounded disorder. Formulate an invariant that survives row scrambles
and gives the same extreme-rank / fringe contracts needed by `NodeSpec`.

**Acceptance:** state a precise replacement for the monotone-column intermediate representation, prove a
one-round preservation/transport lemma on 0-1 inputs, and give its per-node depth budget. Do this before
attempting a large Lean integration.

## UB-05 — Optimize branching factor and number of rounds jointly

**Priority:** P2 · **Status:** research · **Scope:** global schedule and local separator.

The current schedule uses three ordinary stages per factor-64 scale. For a proposed scale factor `b`,
number of separator stages `r`, and per-stage depth `L`, compare the actual global charge
`r * L / log_2(b)` together with root/final costs and geometry constraints. Do not compare only the
smaller matrix height: extra scrambles add full column sorts. Existing two- and three-scramble numerical
screens are useful starting points but are not global proofs.

**Acceptance:** a reproducible rational parameter sweep for plausible `b` and `r`, with all fringe,
failure-budget, and scaling constraints included, and a short list of candidates worth formalizing.

## UB-06 — Improve expander/halver primitives for this interface

**Priority:** P2 · **Status:** research · **Scope:** local primitive plus composition.

Expander-based halvers can replace large sorting operations only if they provide the required two-sided,
rank-sensitive error guarantees at lower depth and fit the scheduler's fringe budget. Compare explicit
expander families, direct counting-based halvers, and multiway halvers against the actual `NodeSpec`
contracts. The existing AKS/multiway notes have promising local cores but do not yet meet the binary
bulk/fringe interface or give an end-to-end schedule.

**Acceptance:** a concrete network family with proved size/depth/error bounds at relevant finite
parameters, plus a composability argument into the current node contract or an explicit revised contract.

## UB-07 — Tapered stranger invariant

**Priority:** P3 · **Status:** parked · **Scope:** redesign the global correctness invariant.

The older [tapered-invariant note](few-hundred-tapered-invariant.md) explores allowing stranger mass to
decay geometrically with rank distance instead of imposing a tiny uniform per-stage error. Its estimates
were calibrated to the 1770-era one-round construction. Recompute them against the 1419 two-round
baseline and current fringe lemmas before relying on the old projected slopes.

**Acceptance:** an explicit invariant and parameter table that includes the fringe costs and predicts a
coefficient below 1200 with credible slack. Only then decide whether to formalize.

