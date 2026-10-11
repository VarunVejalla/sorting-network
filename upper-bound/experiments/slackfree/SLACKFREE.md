# Slack-free (non-uniform block) flow tables: exact feasibility study

Research note, 2026-10-10. Hand derivation plus exact-arithmetic Python. No Lean was touched and
nothing is proved in Lean. Page numbers are Chvátal DCS-TR-294 **printed** pages (PDF page − 1).
Scripts are in this folder; outputs are `*.out`.

## VERDICT

1. **The schedule slack is real, not only an accounting artifact, and a non-uniform table removes
   it physically.**
   * With *perfect* separators, the current (uniform) table creates order-0 outsiders on every
     stage, a worst node peaks at 0.14–0.96 × slackCoeff·c per stage (`explicit.out`, 4 small parameter sets).
   * The non-uniform "cut-layout" table **D2** (§2) creates **zero** outsiders over the whole run
     in all 4 cases.
   * D2 is exactly integral and conserves wires at k = 64 for every triple tested (`compressed.out`).
2. **Chvátal's invariant P cannot certify it.** This is a theorem-level obstruction (§3).
   * Any proof that uses only P, exact wire counts and the Lemma 4.1/4.2 counting (that is,
     *upper* bounds on how many keys a node holds per child) faces an unavoidable residual,
     whatever the block sizes:
     **r\* = (k−1)/(2A²k²)**, against today's slackCoeff = (Aνk−2Aν+1)/(2A²k²).
   * So the slack shrinks only by the factor ≈ 1/(Aν).
   * The bound is tight: design P attains it exactly (checked numerically).
   * At (6,7,6), r\* = 15.9 μ against a (4.2) budget of 0.61 μ, so **(6,7,6) is infeasible by
     26×**.
3. **Best slopes**, with stage depth 3·T(L+1). "Certified" means the window L = 42 with
   ε_B = 1/59e6 (BULK2); other windows use the BULK2-calibrated ε_B(m) *model*.

   | route | what must be proved | best triple, certified L = 42 | best triple, model windows |
   |---|---|---|---|
   | R0 today | — | (6,12,6) **1419** | 1419 |
   | R1: one-sided, optimal non-uniform table (design P) | new table + generalized Lemmas 3.1/4.1/4.2; **same invariant P** | (6,10,6) **1261.3** | (6,8,5) 1148 (L=39), (6,10,6) 1204 (L=41) |
   | R2: D2 + new two-sided invariant Q (κ=1) | R1 + a new invariant about where ancestral keys sit | (6,8,6) **1103.7** | (6,7,5) 1014 (L=38) |
   | R3: zero residual (tapered NOTES assumption) | not achievable (§3, §4) | (6,7,6) 1024.8 | (6,6,5) 984 |

   (6,7,6) is infeasible under R1, and under R2 with κ = 1. Under R2 with κ = ½ it is feasible
   only at L = 46, giving slope 1222.
   **The 1025 figure in tapered/NOTES.md is not reachable.** The realistic gains are:
   * ~11 % (1261) without changing the invariant;
   * ~22 % (1104) with a new two-sided invariant.
4. **Lean cost** (§6).
   * R1: rewrite the flow table as a per-node recursion, since node types are no longer
     enumerable: 135–430 hash-consed node classes at d = 24, against 5 `NodeShape`s today.
     Also generalize `NodeSpec`/`NodeGeom` to unequal row blocks and redo
     Lemma 3.1/4.1/4.2/BadSend with per-child counts and new numerals. Estimate **~2.5–4k
     lines touched/new**.
   * R2: add the new invariant Q and its induction, a further **~1–2k lines**, at high risk.

## 1. Where the slack enters, and why

**Notation** (pp. 7–8). c = c(i,t) ∝ A^iν^t. An interior node has
* a = (1−1/(A²k²))c wires;
* π = (Aνk−1)c/(A²k²) sent to the parent, half from each fringe (F1, F2);
* β = (Ak−ν)c/(Ak²) sent to each child.

So a = π + kβ.

**Lemma 4.1** (p. 11). u holds fewer than c/k + Δ₁ keys addressed below a child w, with
Δ₁ = μδkA²c/(1−δ²k²A²). This comes from the exact wire count below w (Lemma 3.1, p. 9).

**Lemma 4.2 proof** (pp. 11–12).
* Write Δ₂ = c/k − β = νc/(Ak²).
* The separator places B_j at positions π/2 + (j−1)β + 1 … π/2 + jβ.
* The keys of children l ≠ j that a perfect sort can push into B_j number at most
  μc + (k−1)Δ − π/2. The worst case is j = 1 or j = k: the end block has the fringe on one side.
* Then (k−1)Δ₂ − π/2 = (Aνk−2Aν+1)c/(2A²k²) =: slackCoeff·c (`StageKernel.slackCoeff`,
  `Wires31.NodeFacts.slack`).

This term sits inside (4.2) (p. 12) and in Lean in `cond42_scaled`, through
`hBadSend0 … + slackBound`.

**Mechanism.** By counting, every child range holds ≈ c/k keys in u. The window between the
fringes has a − π positions split into k equal blocks β < c/k, and the fringes take π/2 from
child 1 and π/2 from child k. So cut j sits at π/2 + jβ, against the true boundary ≈ j·c/k. The
drift is π/2 − jΔ₂, which runs from +π/2 down to −π/2. A perfect sort then fills B_1 with ≈ π/2
child-2 keys (and B_k with child-(k−1) keys).

`run_tables.out`: the worst one-sided residual computed from the actual integer flows equals
slackCoeff exactly, for every triple and d.

## 2. The non-uniform table (exact bookkeeping)

**Deficit.** For each node y, define G_y(t) = R_y − W_y(t), where R_y = k^{d−level} is the size
of y's key range and W_y is the number of wires in subtree(y). All of the following are exact:
* a_x = Σ_l G_l − G_x.
* The Lemma 4.1 count for child l is U_l = G_l, replacing c/k.
* x sends b_l = U_l − θ_l to child l, with Σθ_l = π_x + G_x.
* The new deficits are G_l ← θ_l and G_x ← G_x + π_x.

So any choice of θ gives an integral table that conserves wires, provided π is even and b ≥ 0.
π keeps Chvátal's values, so (4.4) is untouched.

Lemma 3.1 (p. 9) becomes "W_x = R_x − G_x". Its two cases are:
* top nodes have G = 0;
* every other node has G_x(t) = θ_x(parent, t−1).

**Design U (Chvátal).** θ_l = U_l − β. This reproduces all 855 rows of
`scratch/flow_table2.txt` exactly (`flowsim.py`), and `compressed.py` reproduces `allocation`
at every node.

**Design D2 ("cut layout").**
* The keys of x's range outside the children's subtrees form a virtual sorted list
  [0, ΣU_l), in which child l owns the interval I_l.
* The ancestral share of x consists of the keys of x's range that sit above x. It is the lowest
  gL and the highest gH of that list (gL + gH = G_x).
* Cut off gL + π/2 at the bottom and gH + π/2 at the top. Child l gets the part of I_l that
  remains, and inherits as its own gL/gH the parts of I_l that were cut off.
* Away from the bottom this gives:
  * end blocks U − π/2 − G_x on x's own side and U − π/2 on the other;
  * interior blocks U_l.
* At sparse bottom nodes (π/2 > R_child) the fringe consumes whole children, which then receive
  0 wires. A naïve "end block = U − π/2" rule goes negative there (`run_tables.out`, design D2).
* Checks:
  * explicit tree, k ≤ 8: integral, b ≥ 0, conservation, and **zero outsiders with perfect
    separators**;
  * k = 64 hash-consed (`compressed.py`, validated against the explicit tree): integral, b ≥ 0,
    π even, conservation;
  * a/c ≤ 1.000002 / 1.00003 / 1.00014 / 1.0006 / 1.0038 for y = 12/10/9/8/7 (z = 6).

**Separator geometry.**
* Property B2 (`HasPackSemanticPropertyB2`) holds for every row threshold 1 ≤ i ≤ m. Only
  `packSpec2_high/low` specialize it to `blockBounds π τ` (65 equally spaced points). Arbitrary
  row-aligned boundaries are therefore free semantically.
* `NodeGeom` must become m = 2f + Σ_j b_j (rows), not m = 2f + 64b.
* Exact D2 sizes are sometimes not multiples of any n with 2^42 < a/n ≤ 2^43. This affects up to
  ~30 % of the large senders at (6,12,6) and d = 24, and none at (6,7,6) or (5,7,5).
* The fix is to round the blocks to row multiples. The residual is ≤ 2n ≤ 2^-41·a per block,
  which is < 10^-3 μ and negligible. The cost is that the table becomes a recursion with
  rounding.

## 3. Why P cannot see the removal: r\* = (k−1)/(2A²k²)

**The adversarial state.** Chvátal's induction (P, p. 10) bounds only outsiders. For sender x,
consider any outsider-free state that agrees with all wire counts but places the G_x keys of x's
range that sit above x into *arbitrary* child ranges. This state satisfies P.

**Lower bound at one node.** Cut j sits at a fixed position, but Low_j (the number of x's keys
below range j+1) can be anything in [Σ_{l≤j}U_l − G_x, Σ_{l≤j}U_l]. Put
* T_j = θ_1 + … + θ_j,
* L_j = T_{j−1} − π/2 (keys from lower ranges spilling into B_j),
* R_j = π/2 + G − T_j (keys from higher ranges spilling into B_j).

The worst spill into B_j is L_j⁺ + R_j⁺. If every block had spill < ρ < G:
* T_j ≥ π/2 + G − ρ already at j = 1;
* every θ_j with 1 < j < k must be ≥ G − ρ, and θ_k ≥ π/2 + G − ρ;
* hence π + G = Σθ ≥ π + k(G − ρ).

So **ρ_x ≥ (k−1)G_x/k**, and the end child inherits G_{x₁} = θ_1 ≥ π_x/2 + G_x − ρ_x.

**Along an end-chain.** Here c grows by Aν per link and π/c = (Aνk−1)/(A²k²). Write r = sup ρ/c,
p = π/c and g = G/c.
* Steady state gives g ≥ (p/2 − r)/(Aν − 1).
* Combined with r ≥ (k−1)g/k: r ≥ (k−1)p/(2(kAν−1)) = **(k−1)/(2A²k²)**.

**Tightness.** Design P attains this exactly: θ_end = π/2 + G − r\*c and
θ_int = (2r\*c − G)/(k−2). `explicit.py` measures residual = r\* exactly for (2,3,2), (2,4,2),
(2,5,2) and (3,4,3), with no negative blocks.

r\*/slackCoeff = (k−1)/(Aν(k−2)+1) ≈ 1/(Aν). That is 1/64 at (6,12,6) and ½ at (6,7,6).

The naïve D2 under one-sided accounting is *worse*. Its residual is ≈ G ≈ (π/2c)/(Aν−1), which
equals 1.02 × slackCoeff at (6,7,6) (`run_tables.out`).

Beating r\* therefore needs an invariant that knows the ancestral keys are *extreme* keys (§4, R2).

## 4. The new (4.2) and feasibility (exact Fractions, `feas.py`)

Common choices:
* k = 2^x, A = 2^y, ν = 2^-z;
* μ = (1−2^-10)·min((4.3) ν/(Ak²), (4.4) ½δ_F(Aνk−1)/(A²k²)) with δ_F = 128/4095;
* ε_F = 1/86e6, proved for 131040 ≤ f < 8.5e9;
* δ = the smallest value satisfying (4.5), ε_F/(Aν) + δ²Ak/ν ≤ δ (p. 13), with δkA < 1;
* sib = δkA²/(1−δ²k²A²).

New (4.2) (p. 12, multiplied by Aν):

  μ + (k−1)μ·sib + μδA²k + **res** + ε_B·η ≤ μAν

| | res | η (a ≤ ηc) |
|---|---|---|
| R0 | (Aνk−2Aν+1)/(2A²k²) | 1 |
| R1 | (k−1)/(2A²k²) | 1 + (k−1)/(2A²k²ν²) |
| R2 | κ(μ + ε_B/2)/(Aν−1), κ ∈ {1, ½} | 1 + 1/(kAν(Aν−1)) (≥ measured) |

**Where R2's residual comes from.** It is the misattribution of x's designed ancestral keys,
summed along the same-side chain (c ratio (Aν)^-r per link). Each link contributes two errors:
* the parent's low outsiders, < μc_p, occupy fringe slots and shift x's composition;
* the parent's F1 receives keys of rank > π_p/2, at most ε_B a_p/2 by B at the cut π/2.

κ = ½ assumes the design centres the unknown outsider count.

ε_B → window L: L = 42 uses the certified 1/59e6; other L use `exchange_rate.eps2_scalar` (model).
The fringe f = m·ν/(2Ak)·(1−1/(Aνk))/(1−(Ak)^-2) must lie in [131040, 8.5e9]. It does for every
row below.

Rows: "infeas." means (4.2) fails for every ε_B ≥ 0, with the residual and the budget base
(budget minus the sibling and δ terms) in units of μ. "max ε_B" is the largest ε_B allowed, and L
is the window used for the slope.

| (x,y,z) | Aν | R0 | R1: max ε_B, L, slope | R2 (κ=1): max ε_B, L, slope | R2c (κ=½) | R3 |
|---|---|---|---|---|---|---|
| (6,12,6) | 64 | 1/5.53e7, L42 (margin 1.07), **1419** | 1/2.15e7, L42, 1419 (fringe floor binds) | 1419 | 1419 | 1419 |
| (6,10,6) | 16 | infeas. (31.1μ > 11.9μ) | 1/2.72e7: L42 **1261.3** / L41 1204 | 1/2.35e7: L41 1204 | 1204 | 1204 |
| (6,9,6) | 8 | infeas. | 1/9.05e7: L43 1237.5 (L42 fails) | 1/2.73e7: L42 1182.5 / L41 1128.8 | same | L40 1076 |
| (6,8,6) | 4 | infeas. | **infeas.** (7.91μ > 2.22μ) | 1/4.18e7: **L42 1103.7** (margin 1.41) / L41 1053.5 | same | 1053.5 |
| (6,7,6) | 2 | infeas. | **infeas.** (15.9μ > 0.61μ) | **infeas.** (1.00μ > 0.61μ) | 1/3.92e8: L46 1222 | L42 1024.8 (margin 1.05) |
| (6,7,5) | 4 | infeas. | infeas. (7.91 > 2.80) | L42 1229.8 / L38 1014 | same | same |
| (6,8,5) | 8 | infeas. | L42 1324.4 / L39 1148 | L42 1324 / L38 1092 | same | same |
| (5,7,5) | 4 | infeas. | infeas. (7.82 > 2.95) | L42 1362 / L37 1067 | L36 1012 | L36 1012 |
| (5,8,5) | 8 | infeas. | L42 1475.8 / L37 1156 | L42 1476 / L37 1156 | same | same |

**Binding conditions.**
* μ is set by (4.4) everywhere except (6,12,6), where (4.3) binds. (4.4) and (4.3) differ by
  < 0.1 % at k = 64.
* Within (4.2), the binding term is:
  * the residual at small Aν;
  * at large Aν, the sibling term (k−1)μ·sib. Because ε_F is fixed at 1/86e6, it forces
    δ ≥ ε_F/(Aν), so sib ∝ 1/ν: 12.3μ at (6,12,6) but 0.385μ at (6,7,6).

**R2 at (6,7,6).** It dies because the chain term alone is ≥ μ/(Aν−1) = μ > 0.61μ.

The tapered model's ε_F = 1/(656f) is *unproved*. With it, δ, sib → 0.012μ and R2c(6,7,6) would
reach ≈ 1073 (L = 43). R2 with κ = 1 stays infeasible.

**Schedule and integrality** (`flowsim.Par`). Corrected general envelopes:
* α\* = (tz − dx + 1 + 3x + y − z)/y, i.e. log(2Ak³ν)/log A;
* ω\* = (tz + x + y − z)/(x+y).

They reproduce Lean `alpha7/omega7/tf7` for d = 14…24. The U tables for all triples above are
integral, with π even, a ≤ c and no negative blocks. Constants for d = 30…80:

| (x,y,z) | tf − d(x+y)/z | meet level | final sorter (Lemma 4.5) |
|---|---|---|---|
| (6,12,6) | −20 | d − 6 | 2^42 |
| (6,10,6) | −13…−15 | d − 4…5 | ≤ 2^36 |
| (6,8,6) | −9…−11 | d − 3…4 | ≤ 2^30 |
| (6,7,6) | −8…−10 | d − 3…4 | ≤ 2^24 |

These are additive constants only.

**Smaller A.**
* The top window is [2k², Ak²/ν].
* (4.3) still gives μc < 1 at the descending top.
* All top and rising-top fringes are integral (rising top has c ≥ 2Ak²/ν, so π ≥ 2k).
* Nodes with a ≤ 2^63 use a single sorter. With y ≤ 8 more levels fall in that class, which
  changes only constants.

## 5. What else used equal block sizes (checklist)

**Unaffected:**
* Lemma 3.2 / (4.3) (p. 10, p. 13): the top has G = 0, π = 0 at descent, and the same c.
* Lemma 4.4 / (4.4) (p. 13): π keeps Chvátal's values.
* (4.5), (4.1).
* Lemma 4.5 / final sorters: subtrees at the final level have G = 0, so W = R and the sorter
  size stays k^{d−λ}.
* Property F (`specJmax = δ_F·π/2`).

**Changed:**
* Lemma 3.1 (exact G recursion, §2).
* Lemma 4.1: U_l = G_l instead of c/k. The proof on p. 11 is unchanged, and Δ₁ is unchanged
  because P is stated with c.
* Lemma 4.2: per-child θ, and the max_j(L_j⁺ + R_j⁺) residual.
* The step "since t ≥ 1, a ≤ c" (p. 12) becomes a ≤ ηc.
* Lean `NodeFacts` (`a_le`, `half: π/2 ≤ 63Δ`, `slack`) is specific to uniform blocks.
* `blockBounds` (65 equally spaced boundaries).
* `NodeGeom` (m = 2f + 64b, template scaling (5.2)/(5.3) with 2^s·b₀).
* `NodeShape`: five closed forms are replaced by 135–430 classes (`compressed.out`
  maxclasses), and the count grows with d.

**R2 only:**
* a new invariant Q: "the designed low/high ancestral keys of x lie in range(x₁)/range(x_k), up
  to mis_x ≤ κ(μ + ε_B/2)c/(Aν−1)";
* its induction uses B at the fringe cut and P at the parent;
* it needs a two-sided count (lower bounds on ancestral keys), which nothing in Chvátal provides.

## 6. Lean work (estimates)

| module | change | lines |
|---|---|---|
| Schedule7 (369) | new (x,y,z) numerals. Capacities are no longer powers of 64 for y ∉ 6ℕ, so the exponent lemmas need redoing. | 200–350 |
| FlowTable (266), FlowSizes7 (451) | per-node recursion G/θ (D2 or rounded P). `FlowSizes.a : ℕ→ℕ→ℕ` becomes per-bag. Integrality and b ≥ 0 by induction. | 800–1200 |
| NodeShape/Wires31 (194) | replaced by inequality facts (G ≤ g·c, a ≤ ηc, prefix offsets) | 250–400 |
| NodeGeom (131), GeometryScale (69) | unequal row blocks; rounding existence for 2^42 < m ≤ 2^43 | 200–300 |
| NodeSpec (36), PackSpec2/PackNodeSpec2 (65) | `blockBounds` becomes an arbitrary row-aligned list (B2 already covers all rows) | 80–150 |
| BadSendReal (434), BadSendField | sorted-placement with per-child τ_j and θ prefix sums | 300–500 |
| Lemma41Real (360), StrangerBounds (159) | per-level `a : ℕ → ℕ` replaced by per-node subtree counts R − G | 200–350 |
| WireFlow (326), ExecPlacement (225), RealBlocks (214), RealInduction (194), KernelSetup (79) | per-node sizes threaded through | 300–500 |
| StageKernel (213) | new numerals; slackCoeff becomes (k−1)/(2A²k²) (R1) | 50–100 |
| DepthSkeleton (54), Certificate/headline | new tf constant and slope | 50–150 |
| **R2 extra** | invariant Q, ancestral-composition lemma, joint induction | 1000–2000 |

**Risks.**
1. ε_B windows below L = 42 are model values. Certified BULK2 exists only for m ≥ 2^42; the 1204
   and 1148 figures need a re-certified two-round B. The L = 42 column is safe.
2. Design P is not type-closed: interior children inherit G-dependent θ. A Lean version would
   prove inequalities on G (with rounding) rather than closed forms.
3. The sparse-bottom cut rule (fringe larger than a child) empties some bottom-level children. It
   is verified for D2; for P it is untested at k = 64.
4. R2's chain-error model (κ) is a derivation, not a proof. A second-order term of size
   ε_B·k (per-block instead of per-cut B) would kill every R2 row with Aν ≤ 4.
5. (6,12,6) gains nothing in slope from R1, because the fringe floor f ≥ 131040 pins L = 42.
   R1 pays off only together with a triple change to (6,10,6).

## Files

* `flowsim.py`: the exact Chvátal table (verifies `flow_table2.txt`, 855/855 rows), the
  general schedule, and the typed simulator (U, D2 without the bottom rule).
* `run_tables.py` → `run_tables.out`, `run_tables2.out`: worst one-sided residual, a/c, G/c.
* `explicit.py` → `explicit.out`: explicit small-k tables, the perfect-separator key simulation,
  and design P.
* `compressed.py` → `compressed.out`: exact k = 64 D2 and U tables by hash-consing (integrality,
  b ≥ 0, conservation, geometry).
* `feas.py` → `feas.out` (model windows) and `feas_L42.out` (L ≥ 42 only): conditions
  (4.2)–(4.5) in exact Fractions.
