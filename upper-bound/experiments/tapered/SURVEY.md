# Survey: invariants of the AKS family, tolerated error, stages per bit

Produced by a read-only survey agent (2026-10-10); numbers are quoted from the repo sources and
have not been re-derived. Sources are cited as `file §section`. "Unknown" means the repo sources do
not state it. pdftotext loses Greek letters in `docs/dcs-tr-294.pdf`, so Chvátal's (4.2) and (4.5)
are read from the Lean `cond42_scaled` and `cond45_scaled` in `upper-bound/best/AKS/Chvatal/StageKernel.lean`.

Notation: lg = log2; k = tree arity; A = capacity growth per level; ν = capacity shrink per stage;
μ, δ = invariant constants (strangers at distance j are at most μ·δ^(j-1) of capacity).

## 1. Comparison table

All invariants are geometric in the stranger distance. None is a flat strict bound.

**AKS 1983.** Primitive: ε-nearsort from ε-halvers on a halving cascade, halvers from expanders
(`aks.pdf` §1, §4). Quality: nearsort ε=1e-6, halver 1e-9, inner halver 1e-15, A=100, "A << 1/ε".
Invariant: "wrongness" w(R); the fraction of a node's registers with wrongness > r is ≤ c·A^(-3r) (OCR).
Stages per bit, depth per stage, coefficient: not stated.

**AKS 1992** (`docs/ajtai1992-multiway-halvers.md`). Primitive: depth-2 k-sorter that is an ε-halver at
the single central cut, ε = c0·sqrt(log k / k) (c0=3 for k≥23, 2 for k≥60). Invariant, tolerated ε,
stages per bit, coefficient: not given. Two bitonic k-sorter layers cost r(r+1) binary layers at k=2^r;
the one-cut error is about 5–8% at k=2^13..2^14 against ~1e-8 needed by Chvátal's `NodeSpec`.

**Paterson** (`docs/paterson.pdf` is the 1987 Warwick report RR89). Primitive: (λ, ε, ε0)-separator from
p levels of ε0-halvers. Quality: sample p=4, λ=1/8, ε0=1/72, ε=1/18, A=3, μ=1/36, δ=1/40; best p=5,
A=4.75, μ=1/50, δ=1/57. Invariant: S_j(B) < μ·δ^(j-1) of capacity (§4 eq. (2)). Tolerated ε: (4)
2A²δ²+ε ≤ νAδ; (5) 2μδA²+2μδA²/(1-4δ²A²)+1/(8A²-2)+μ+ε0/2 ≤ νμA; ν = 2λA+(1-λ)/(2A).
Stages per bit lg(2A)/lg(1/ν): sample <17, best 6.12 ("about 6.15"). Depth per stage <1000. Coefficient <6100.

**Seiferas 2009** (`docs/seiferas.md`). ε-approximate λ-separator from ε0-halvers. Quality: λ=ε=1/99, A=10,
ν=13/20 (alt: A=6.785, λ=1/96.4, ε=1/57.45). Invariant: j-strangers ≤ λ·ε^(j-1)·capacity. Tolerated ε (§5):
ν ≥ 2Aε+1/A; ν ≥ 4λA+5/(2A); plus a cross inequality. Stages per bit (1+lg A)/lg(1/ν) = 6.95 (alt 6.05).
Depth per stage 7×10564 (alt 7×5621). Coefficient 514247 (alt 238198).

**Chvátal 1992** (DCS-TR-294; Lean 1830/1770/1419). Primitive: m×n scramble (sort columns, row permutation,
sort columns); Property B (bulk, ε_B) and Property F (fringe, ε_F, j ≤ δ_F|F|). Quality: k=64, A=4096, ν=1/64.
Paper (§7): ε_B ≈ 1.25e-8, ε_F = 1/(8e7), δ_F=128/4095. Lean (`StageKernel.lean`): ε_B=1/5.9e7,
ε_F=1/8.6e7, μ=(1-2^-10)·2^-30, δ=1/5.3e9. Invariant: outsiders of order r < μ·δ^r·capacity (tapered!).
Conditions: (4.1) ε* ≤ μ/k; (4.3) μ ≤ ν/(Ak²); (4.4) μ ≤ ½δ_F(Aνk-1)/(A²k²); (4.2) bulk; (4.5) fringe.
Stages per bit (x+y)/(xz) = 0.5 at (6,12,6). Depth per stage 3660 (paper), 3540 (Lean 1770), two-round 2838.
Coefficient 1830, 1770, 1419.

**Legacy Lean Paterson** (`upper-bound/alternatives/legacy`). Separator depth 263+155+167+187+217 = 989; A=19/4,
μ≈0.02, δ=1/57, ν=0.707; stages per bit 6.5 (13⌈k/2⌉); coefficient 6990.5 = (13/2)·989+561+1.

## 2. How the tolerated ε is tied to the tree parameters

Every construction limits the tail/fringe error by shrink × growth × decay ratio, ε_tail ≲ ν·A·δ minus
a second-order term. δ is capped by the sibling-contamination term: Chvátal (k−1)·μ·δ·kA²/(1−δ²k²A²) against
a budget μ·Aν, so δ ≲ ν/(k²A). μ is capped by (4.3), μ ≤ ν/(Ak²). With μ ≈ ν/(Ak²) and δ ≈ μ/5:
**ε_B ≲ νAμ = (ν/k)²**, i.e. 2^-24 at (64, 4096, 1/64) (paper (7.1)/(7.2): ¼·k^-4 = 2^-26).

Budget split of (4.2) at the Lean values (units of 1e-8; budget 64μ = 5.96):

| term | value | share |
|---|---:|---:|
| schedule slack ≈ 1/(2Ak²) | 2.89 | 48% |
| ε_B | 1.69 | 28% |
| sibling term 63·μ·siblingFactor | 1.19 | 20% |
| μ | 0.09 | 2% |

About half the budget is rounding/schedule slack that does not depend on the separator; raising ε_B alone by
~3.5× exhausts it. (LEDGER M2′ reports LHS/μ = 0.960; the survey evaluates ~0.91 — constants differ slightly.)
Fringe floor: any scramble-based F contract needs ε_F(2f+1) > 1 (`docs/chvatal-fringe-obstruction.md`).

## 3. Answers

(a) All constructions use a tapered (geometric in distance) invariant; Chvátal's δ ≈ 1e-10 (≈ μ/5) is very steep.
The 10^6 gap between Paterson's ε (≈ 0.04) and Chvátal's (≈ 1.7e-8) comes from k=64, A=4096 versus k=2, A≈5.

(b) ε–ν relations: Paterson ε ≤ νAδ − 2A²δ²; Seiferas ν ≥ 2Aε+1/A; Chvátal ε_B ≲ μAν − slack − sibling,
ε_F ≲ Aνδ, μ ≤ ν/(Ak²), hence ε ~ (ν/k)². In Chvátal's (x,y,z) the ε tolerance is ≈ 2^(−2(x+z)).

(c) With a sort-based separator whose errors are local: the sibling term comes from the parent's contents, not
from separator errors, so locality does not shrink it; locality might relax Property B (65 cuts) to a
per-neighbour statement (plausible, unchecked) — at best the ε_B share (28%) relaxes. The order-r outsider bookkeeping
and (4.5), ε_F ≲ Aνδ, with the 1/(2f+1) floor, do not change from bulk locality. Schedule slack is unchanged.

(d) "~100 coefficient" attributed to Komlós — all unverified: Chvátal DCS-TR-294 §9 ("around 60 to 100 in place of
the 1830 in Theorem 1.1; less than 10 in place of the 48 in Theorem 1.2"); `docs/seiferas.md` §7 ("100 log₂ n privately
claimed by Komlós"); `docs/ajtai1992-multiway-halvers.md` (a derived conversion c_M<10 with Batcher at M=2^11..2^19
giving 60..100, "not a recovered theorem"). No source gives parameters.

## 4. Open items

Re-read garbled (4.2), (4.5), AKS 1983 exponent and Paterson (3) from page images; reconcile 0.91 vs LEDGER 0.960;
re-derive the (ν/k)² scaling symbolically before using it in the ε → slope table.
