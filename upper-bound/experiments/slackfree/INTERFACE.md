# R1 in Lean: the `FlowFacts` interface and a staged plan

Scoping note, 2026-10-10. Read-only pass over `upper-bound/best/AKS/Chvatal/*.lean` (paths below
are relative to that folder) and over `SLACKFREE.md` with its outputs. No Lean was edited and
nothing was built.

## 0. Verdict

* **The all-d proof is feasible, but not with closed forms.** Replace `NodeShape` by a
  per-bag recursion. Prove its facts by induction on `t` with **scale-free inequality
  invariants**, roughly `0 ≤ G_x(t) ≤ g*·c(x.l,t)` plus a few role-specific bounds. Their
  transitions are linear and close by `linarith`/`norm_num`. Bottom-node bounds use exponent
  arithmetic via `omega`, as `exp_*` does today.
  * Nothing is enumerated in `d`.
  * `decide +kernel` is not needed.
  * The 135–430 hash-consed classes are irrelevant to the proof.
* **Design choice: implement D2 (cut layout), not design P.** P is fractional, untested at
  k = 64 and not type-closed. D2 is integral by construction, and `compressed.py` already
  validates it at k = 64 (b ≥ 0, conservation).
  * Its one-sided residual is ≤ `G_x` (proved in §3.2).
  * Measured `max G/c` is 7.94e-9 at (6,10,6), which is 1.08 r\* ≈ 2.1 μ. At (6,12,6) it is
    4.73e-10, which is 1.03 r\*.
  * The (6,10,6) (4.2) budget at L = 42 is about 11.9 μ minus ε_B ≈ 4.6 μ, which leaves room
    for ≈ 7 μ. So D2 suffices, and P's optimality is not needed.
  * SLACKFREE §3 says "D2 is worse". That holds only at small Aν (6,7,6), where it does not
    matter for R1.
* **Cost is above the 2.5–4k estimate.** My estimate is **≈ 5–8k Lean lines new or changed,
  centre ≈ 6k**. Two items are underestimated in SLACKFREE §6:
  * threading per-bag sizes through ~20 modules, since `FlowSizes` is per-**level** today
    (`FlowSizes7.lean:23`);
  * the rounding/geometry invariant for big nodes, especially bottom nodes.
* **Go, conditionally.** Do it only after a Stage-0 Python gate (§4) has:
  * frozen the exact rounded D2 rule;
  * machine-checked that a finite-role scale-free invariant is inductive, bottom roles included.

  If Stage 0 cannot find one, stop.

## 1. What each module consumes from the flow table

"EB" = specific to equal blocks (one `down` value for all 64 children). "Lvl" = indexed by level
only. "A" = depends on the (6,12,6) constants or schedule but not on block shape.

| module | facts consumed (name / shape) | EB? |
|---|---|---|
| `Schedule7` (369) | Defines `capacity` with literals 4096, 1/64 (`:23`). Also `capacityRatio` (`:40`), `tf7 = 3d−20` and `meetLevel7` (`:55`), `alpha7`/`omega7`, `Active`. Uniform `allocation` (`:190`), `capacity_eq_pow` (64^e, `:226`), `lemma32_schedule7` (c ≤ 2^30, `:272`), `lemma31_of_total` (per-level Lemma 3.1, `:321`) | allocation and Lemma 3.1: EB, Lvl. Rest: A |
| `FlowTable` (266) | `flowUp`/`flowDown` per level. `flow_send7`: a = π + 64τ (`:108`). `flow_conservation7` (`:172`) | EB |
| `FlowSizes7` (451) | `structure FlowSizes` (`:23`): `a/up/down : ℕ→ℕ→ℕ`, `hsplit a = up + 64*down`, `hcons … + 64*up(l+1)`. `NodeShape` with 5 closed forms (`:87`). `shape_rat`, `node_shape` (`:266`), `exp_top/exp_nontop/exp_top_rise`, `omega7_lt_d`, `flowA7_two`, `cast_flow*`. `NodeShape.even`/`.split` | EB, Lvl |
| `Wires31` (194) | `total_mass`: Σ 64^l a_l = 64^d. `hpar7` (wrong parity empty). `hwires7` (Lemma 3.1: subtree count `(64^d/64^i − c)/64`, `:78`). `NodeFacts {a_le, nonneg, up_le, half: π/2 ≤ 63Δ, slack: 63Δ−π/2 ≤ slackCoeff·c}` (`:131`). `node_facts` (`:184`) adds the fringe dichotomy and the Lemma 4.1 source (`Inner ∧ c/64 ≤ τ+Δ` or `64^(d−i−1) ≤ τ+Δ`) | EB (Δ is the uniform per-child deficit) |
| `NodeGeom` (131) | `NodeGeom` with `hm : m = 2f + 64b`, `hdown : down = b*n` (`:13`). `NodeShape.geom` templates (`:74`). `nodeGeom_exists` (`:121`) | EB |
| `GeometryScale` (69) | `exists_pow_scale`, `scaled_m_eq` (any k), `scaled_fringe_big_ratio` | generic, reusable |
| `WireFlow` (326) | `FlowSizes` fields `hsplit, hcons, hup_even, hup_root, hdown_leaf, ha_root, ha_init`. `downSet s π τ j = blockOf (π/2 + jτ) (π/2 + (j+1)τ)` (`:27`). `downSet_card` needs `card = π + 64τ` (`:83`). `cover` divides by τ (`:101`). `parentPart` takes block `b.x % 64` of `F.down (b.l−1)` (`:125`). `wireSets_inv` (`:214`) | EB, Lvl |
| `ExecPlacement` (225) | `execPlacement_card = F.a b.l t` (`:85`). `fromParentK` (`:92`). `mem_image_downSet_iff` with window `π/2 + jτ` (`:209`) | EB, Lvl |
| `StageNet`, `Tree`, `RealNetwork`, `FinalSorts` | nothing table-specific (generic over `F` or the bag sets) | — |
| `NodeSpec` (36) | `blockBounds π τ` = 65 equally spaced points (`:18`) | EB |
| `NodeKeys` (129) | `intruder_keys`: `a = π + 64τ`, `bLow` at π/2+jτ, `bHigh` at π/2+(63−j)τ (`:92–110`) | EB |
| `PackSpec2` (232), `PackSpec`, `FlipSpec`, `PackNodeSpec2` (65), `RealNets.packNodeSpec` | Statements use `blockBounds (2fn) (bn)` and `hmfb : m = 2f+64b`. The proof only uses p = i·n (`PackSpec2.lean:118–122`) | EB in statement only |
| `TwoRoundHyp`/`TwoRoundProof` | `_hshape : m = 2f+64b` (`TwoRoundHyp:23`). Used only via `ScrambleGeometry.ofShape … 64 … hshape` (`TwoRoundProof`). That needs only `f ≤ m` (`MatrixBridge:317`) | EB in statement only (use k = 1, b = m−2f) |
| `StrangerBounds` (159) | Uses P only. `capacity_two_levels` (4096, `:19`). `sent_outside_le` is generic | A |
| `Lemma41Real` (360) | `card_subtreeKeys`/`subtree_bad_le(_parity)` with `a : ℕ → ℕ` per level and `hpar` (`:128–198`). `sibling_sum_le` (4096, `:243`). `keys_below_child_le` (`:296`): hypothesis `hwires` (per-level Lemma 3.1), conclusion **`c/64 + μ·sib·c`** | EB, Lvl |
| `BadSendReal` (434) | `BW.window_wrong_le`: k equal windows τ, `hM ≤ τ+ρ`, `hpos` (`:122`). `window_real`: `K.card = π + 64τ` (`:257`). `bad_send0_real` (`:334`): `F.hsplit`, `hup_even`, `wireSets_card`, `intruder_keys`, window `π/2 + jτ`, `hM: native_j ≤ F.down + ρ`, `hpos` | EB (core) |
| `BadSendField` (147) | `node_facts` (Δ, `.half`, `.slack`, `.a_le`), `hM_keys` (`hwires7`, `hpar7`, `Inner`), `hM_pow`. `specEB` with a ≤ c, `slackCoeff` (`:72–145`) | EB |
| `FringeSendReal` (200) | `ha : card = up + 64·down`. Block j lies inside the middle via `(j+1)τ ≤ 64τ` (`:151`) | EB (mild) |
| `FringeSendField` (90) | `node_facts` fringe dichotomy `(π=0 ∧ (l=0 ∨ c≤2^30)) ∨ 4095c/2^36 ≤ π` (`jmax_ok :42`), `flowSizes7_split` | via NodeShape. Content is generic (π keeps Chvátal values) |
| `KernelSetup` (79) | `RealSpecs` per level (`:21`), `specEB t (a l t)`, `specJmax`. `cond44_real`, `mu_real_mul_le_one` (2^30). `fromParentK_eq_empty` (down = 0) | Lvl, A |
| `StageKernel` (213) | `invMu, invDelta, invEpsB, invEpsF, siblingFactor` (4096), `slackCoeff` (`:38`). `cond42_scaled` assumes ε_B·a ≤ ε_B·c (`:42`). `cond45_scaled`. Kernel fields carry 4096 and 1/64 literals. `outsiderBound_step_of_kernel` | slackCoeff + a ≤ c: EB. Rest: A |
| `RealKernel` (61) | generic given the kernel fields | — |
| `RealNets` (291) | `nodeGood_exists`: `flowSizes7` per level, `nodeGeom_exists`, root sizes (`:210`). `realNets` keyed on `n = a b.l t ∧ 0 < down b.l t` (`:239`) | Lvl |
| `RealInduction` (194) | `P_one`: root sizes (`down=64^(d−1)`, `up=0`, `a=64^d`), `a b 1 = 0` for l ≠ 1, `capacity d 1 1 = 64^(d−1)` (`:46–150`), `hpos`. `real_purity`: `capacity_meet7 = 64^6` at level d−6 (`:183`) | A |
| `RealBlocks` (214) | `flowA7_tf` (= 64^6 at level d−6, `:40`), `finalS_card = 2^42` (`:91`) | A, Lvl |
| `RealSorter`, `DepthSkeleton` (54) | `tf7 = 3d−20`, `depthBound`, `totalDepth = 8514d − 52375` (`DepthSkeleton:27`) | A |

**The structural EB core** is `FlowSizes`, `NodeShape`, `NodeFacts`, `NodeGeom`, `downSet`,
`blockBounds`, `intruder_keys`, `window_wrong_le`, and `keys_below_child_le`'s `c/64`.
Everything else is either per-level indexing (mechanical) or constants.

## 2. The interface

### 2.1 Generic wire bookkeeping: replaces `FlowSizes`

```lean
/-- Per-bag integer flow table (non-uniform blocks). Generic; no numerics. -/
structure FlowTableB (d tf : ℕ) where
  a    : ℕ → KBag 64 d → ℕ                  -- wires at bag b at time t
  up   : ℕ → KBag 64 d → ℕ                  -- π_b(t)
  down : ℕ → KBag 64 d → Fin 64 → ℕ         -- τ_{b,j}(t)
  ha_root    : a 0 (KBag.root 64 d) = 64 ^ d
  ha_init    : ∀ b, b ≠ KBag.root 64 d → a 0 b = 0
  hup_even   : ∀ t b, t < tf → 2 ∣ up t b
  hup_root   : ∀ t, t < tf → up t (KBag.root 64 d) = 0
  hdown_leaf : ∀ t b j, t < tf → b.l = d → down t b j = 0
  hsplit     : ∀ t b, t < tf → a t b = up t b + ∑ j, down t b j
  hcons      : ∀ t b, t < tf → a (t+1) b =
    (if 1 ≤ b.l then down t b.parent ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩ else 0) +
    (if h : b.l < d then ∑ j : Fin 64, up t (b.child j j.isLt h) else 0)

/-- Prefix offsets: child `j` gets cells `[π/2 + off j, π/2 + off (j+1))`. -/
def FlowTableB.off (F : FlowTableB d tf) (t : ℕ) (b : KBag 64 d) (j : ℕ) : ℕ :=
  ∑ i : Fin 64 with i.val < j, F.down t b i

/-- Deficit `G = R − W` (Lemma 3.1 quantity), in ℚ so that no sign is needed. -/
def FlowTableB.deficit (F) (t) (b : KBag 64 d) : ℚ :=
  (64 : ℚ) ^ (d - b.l) - ∑ z ∈ subtreeBags 64 d (by norm_num) b, (F.a t z : ℚ)

/-- θ_j = G_child − τ_j and the one-sided Lemma 4.2 residual of window j (SLACKFREE §3). -/
def FlowTableB.residAt (F) (t) (b) (hb : b.l < d) (j : Fin 64) : ℚ :=
  max 0 ((∑ i with i < j, (F.deficit t (b.child i i.isLt hb) - F.down t b i)) - F.up t b / 2) +
  max 0 ((∑ i with j < i, (F.deficit t (b.child i i.isLt hb) - F.down t b i)) - F.up t b / 2)
```

* All `FlowTableB` fields are **generic**. The `hsplit`/`hcons` sums replace the `64*`.
* The uniform table instantiates it by `a t b := flowA7 d hd b.l t` and
  `down t b _ := flowDown7 d hd b.l t`. Every field then follows from the existing
  `flowSizes7_*`, with `∑ j, c = 64*c`.

### 2.2 Numeric facts: replaces `NodeShape`, `NodeFacts`, `node_facts`, `hwires7`, `hpar7`, `nodeGeom_exists`, `flowA7_tf`

```lean
structure FlowFacts (F : FlowTableB d tf) (cap : ℕ → ℕ → ℚ) (λ : ℕ)
    (η rT upFrac topCap : ℚ) : Prop where
  parity : ∀ t b, 1 ≤ t → t ≤ tf → b.l % 2 ≠ t % 2 → F.a t b = 0          -- generic
  a_le   : ∀ t b, 1 ≤ t → t < tf → 0 < ∑ j, F.down t b j →
             (F.a t b : ℚ) ≤ η * cap b.l t                                -- generic shape; η = 1 today
  resid  : ∀ t b (hb : b.l < d) j, 1 ≤ t → t < tf → 0 < F.down t b j →
             F.residAt t b hb j ≤ rT * cap b.l t                           -- replaces NodeFacts.slack
  fringe : ∀ t b, 1 ≤ t → t < tf → 0 < ∑ j, F.down t b j →
             (F.up t b = 0 ∧ (b.l = 0 ∨ cap b.l t ≤ topCap)) ∨
             upFrac * cap b.l t ≤ F.up t b                                 -- generic (π unchanged)
  geom   : ∀ t b, 1 ≤ t → t < tf → 0 < ∑ j, F.down t b j → 2 ^ 63 < F.a t b →
             Nonempty (NodeGeomV (F.a t b) (F.up t b) (F.down t b))       -- EB today; unequal-blocks form
  root   : F.up 0 (KBag.root 64 d) = 0 ∧ ∀ j, F.down 0 (KBag.root 64 d) j = 64 ^ (d-1)
  one    : ∀ b, b.l ≠ 1 → F.a 1 b = 0
  final  : ∀ b, F.a tf b = if b.l = λ then 64 ^ (d - λ) else 0            -- RealBlocks/purity
```

**No `hwires`/Lemma 3.1 field is needed.** The deficit is *defined* as `R − W`. Lemma 4.1 then
becomes the generic theorem

`native_j(u) ≤ deficit (u.child j) + μ·sib·c(u.l,t)` for every `u` with `u.l % 2 = t % 2`.

Its proof is today's `keys_below_child_le` (`Lemma41Real:296`) with `hScard` replaced by the
definition. It needs no `Inner` split and no `hM_pow`, because empty child subtrees give
`deficit = R`. The only table fact it uses is `parity`, through `subtree_bad_le_parity` per bag.

`NodeGeomV` replaces `NodeGeom` (`NodeGeom:13`):

```lean
structure NodeGeomV (a up : ℕ) (down : Fin 64 → ℕ) where
  m n f : ℕ
  b : Fin 64 → ℕ
  hm : m = 2 * f + ∑ j, b j
  ha : a = m * n
  hup : up = 2 * f * n
  hdown : ∀ j, down j = b j * n
  hm1 : 2 ^ 42 < m
  hm2 : m ≤ 2 ^ 43
  hn : 16 ≤ n
  hf : f = 0 ∨ (131040 ≤ f ∧ Even f)
```

**What stays a parameter, not a field.** These are constants of the instance, consumed by
`StageKernel` and `KernelSetup`:
* `cap`, `tf`, `λ`;
* `η`, `rT` (the old `slackCoeff`), `upFrac` (4095/2^36 today), `topCap` (2^30 today).

`cond42_scaled` becomes

`(μ + 63μ·sib + rT + ε_B·η)·c + μδA²k·c ≤ μAν·c`.

`slackBound := rT·c`. The ε_B term is ε_B·η·c.

**The current table satisfies `FlowFacts`** with η = 1, rT = `slackCoeff`, λ = d−6. The
residual follows from `NodeFacts`:
* for interior/top children, deficit = c/64, so θ_i = Δ for every i;
* for bottom children, deficit = 64^g, so θ_i = 64^(h+2) = Δ.

Hence `residAt = (jΔ−π/2)⁺ + ((63−j)Δ−π/2)⁺ ≤ 63Δ − π/2 ≤ slackCoeff·c`, by `half` and `slack`.

### 2.3 Statement changes downstream

* **`WireFlow`.** Use `downSet s π off j := blockOf s (π/2 + off j) (π/2 + off (j+1))`.
  * `downSet_card` needs `s.card = π + ∑ τ`, with `off` monotone.
  * `disjoint_downSet` comes from monotonicity of `off`.
  * `cover` replaces `(r−π/2)/τ` with `∃ j < 64, off j ≤ r−π/2 < off (j+1)`, using
    `Nat.find` on the monotone prefix sums.
  * **Yes, child j gets ranks `[π/2 + Σ_{i<j} τ_i, π/2 + Σ_{i≤j} τ_i)`. This generalizes
    simply** (~100–150 changed lines).
  * `parentPart`/`childPart`/`wireSets` become per bag: `down t b.parent ⟨b.x % 64,_⟩`.
* **`ExecPlacement`.** Use `execPlacement_card = F.a t b`. `fromParentK` and
  `mem_image_downSet_iff` take windows `π/2 + off j`. This is mechanical.
* **`NodeSpec`.** Parametrize by a boundary set: `NodeSpec a π (bds : Finset ℕ) net EB Jmax εF`.
  * `intruder_keys` takes `p₁ := π/2 + off j ∈ bds` (for `bLow`) and
    `p₂ := π/2 + Σ_{i>j} τ_i ∈ bds` (for `bHigh`, since `a − p₂` is the window end). Drop
    `ha : a = π+64τ`.
  * `RealSpecs` supplies `bds := image (π/2 + off ·) ∪ image (π/2 + suffix ·)`.
* **`PackSpec2`, `PackNodeSpec2`, `FlipSpec`, `RealNets.packNodeSpec`.** Restate the bounds as
  `∀ p, n ∣ p → p ≤ m*n → …`. The proof is unchanged, since it already writes p = i·n
  (`PackSpec2:120–122`). `NodeGeomV.hdown` gives `n ∣` every boundary.
  * Drop `hmfb` and `TwoRoundHyp._hshape`, or weaken them to `2f ≤ m`.
  * In `TwoRoundProof` call `ScrambleGeometry.ofShape m n (m−2f) f 1 …`.
  * The B2/F2 certificates are untouched.
* **`BadSendReal`.**
  * `BW.window_wrong_le` becomes a prefix-sum lemma. Given `hM : ∀ j', N_j' ≤ U_j' + ρ`, the
    output is:
    * window `[π/2 + T_j, π/2 + T_{j+1})` (T_j = Σ_{i<j} τ_i);
    * bound `OL + OR + 63ρ + (Σ_{i<j}(U_i−τ_i) − π/2)⁺ + (Σ_{i>j}(U_i−τ_i) − π/2)⁺`.
  * `hpos` disappears, because positive parts replace it.
  * `lower_count_le` generalizes verbatim, with `j*(τ+ρ)` → `Σ_{i<j}(U_i+ρ)`. The *key*
    intervals `Ulo + j·64^(d−l−1)` stay uniform; they are tree ranges.
  * `bad_send0_real` takes `hM` with `U_j' := deficit (q.child j')` and concludes
    `strangers + 63ρ + residAt + 2EB`. **Every `down` must become `down … j`.**
* **`Lemma41Real`.**
  * `a : ℕ → ℕ` becomes `a : KBag → ℕ`, with `hcard`/`hpar` per bag.
  * `keys_below_child_le` drops `hwires` and `hu`-style `Inner`, and concludes
    `deficit w + μ·sib·c`.
* **`BadSendField`/`FringeSendField`.** Rewrite over `FlowFacts`. `FringeSendReal` only needs
  "block j ⊆ middle", i.e. `off (j+1) ≤ Σ τ`.
* **`RealNets`.** Use `nodeNetOf t b`, per bag. `realNets t b n` is guarded by
  `n = F.a t b ∧ 0 < Σ_j F.down t b j`.

## 3. The new table: definition and how to prove it for all d

### 3.1 Definition (D2, per bag, recursion on t)

State: `st : ℕ → KBag 64 d → ℕ × ℕ`, written `(gL, gH)`, with `G := gL + gH`.

**At t = 0.** The root has `(0,0)`. Every other bag has `(0, R)`, matching `compressed.py`
`initial`.

**Step t → t+1.** For bag b at level i:
* **b active at t.** Set `(gL + π/2, gH + π/2)`, where `π := piSched d i t` is Chvátal's value
  by role (a closed form) and `π = a` at a rising bottom.
* **b's parent p active at t.** Let `S_j := Σ_{i<j} G(sib_i)`, `lo := gL_p + π_p/2`,
  `hi := S_64 − gH_p − π_p/2`. Set `(cl, ch)` with
  * `cl = min(S_{j+1}, lo) − min(S_j, lo)`;
  * `ch = max(S_{j+1}, hi) − max(S_j, hi)`.

  At top-descending parents set `(0,0)`.
* **Otherwise.** Unchanged.

**Derived quantities.**
* `a t b := Σ_j G(child j) − G(b)` (or `R − G` at a leaf).
* `down t b j := |[S_j, S_{j+1}) ∩ [lo, hi)|`, which equals `min/max` arithmetic.
* `up t b := π`.
* Rounding: round `lo`/`hi` to multiples of a grain `γ(i+1, t+1)` (a power of 2 fixed by
  `(i,t)`; see risk R3). That changes only `lo`/`hi`.

**Generic lemmas on this definition** (no numerics):
* (L1) Intersecting the partition `[S_j,S_{j+1})` with `[lo,hi)` telescopes:
  `Σ_j down = hi − lo`, `Σ_j θ_j = lo + (S−hi) = π + G_p`.
* (L2) Consistency invariant by induction on t: an inactive b with no active parent has
  `G(b) = Σ G(children)`, i.e. `a = 0`. This gives `parity`, `hcons`, `hsplit` (given `lo ≤ hi`,
  i.e. `a ≥ π`) and the deficit identity `deficit t b = G_b(t)` (Lemma 3.1).
* (L3) Top bags have `G = 0`. This gives `final` (`a = R` at λ) and the root and `t = 1` facts.

### 3.2 Why the residual is one scalar

For a block j with `down j > 0` we have `S_j < hi` and `S_{j+1} > lo`. Then by (L1):
* `L_j = Θ_j − π/2 ≤ gL`;
* `R_j = π/2 + G − Θ_{j+1} ≤ gH`.

So **`residAt ≤ G_x(t)`**, plus the rounding error, which is at most 2γ·(#cuts). This is
~200 lines of `min`/`max` arithmetic, independent of d. Hence `FlowFacts.resid` reduces to
`G_x(t) ≤ rT·c(x.l,t) − rounding`.

### 3.3 The crux: invariants for all d

There are no closed forms. Fix rationals `g*` (≈ 1.1 r\*), `η`, and per-role bounds. Prove by
induction on t (`Nat.rec`, mirroring `wireSets_inv`):

* **(I1) Every active non-top bag has `G ≤ g*·c` and `0 ≤ gL, gH`.** The transition (when no
  single child spans both cuts):

  `G_x(t) = cl+ch ≤ π_p(t−1)/2 + max(gL_p,gH_p) ≤ (p/2 + g*)·c_p`,

  with `c_x(t) = Aν·c_p(t−1)` (`capacity_succ_level/stage`). This closes iff
  `g* ≥ (p/2)/(Aν−1)`, the note's steady state. It is pure `linarith`.
* **(I2) `π ≤ a ≤ η c`, and `a > 0`, at senders.**
  * The sum of the children's G is closed-form apart from `G_x(t−2)`:
    `ΣG_l(t) = Σθ_l(x,t−2) + Σπ_l(t−1) = π_x(t−2) + G_x(t−2) + 64·π_child(t−1)`.
  * So `a_x(t) = closed form + G_x(t−2) − G_x(t)`, which is bounded by (I1).
  * This needs a **role-transition table**: x's role at t−2 versus t, and children's roles at
    t−1. It is finite: top/rise/mid/botDesc/botRise times α/ω step directions, ≈ 20–30
    transitions.
* **(I3) Bottom.**
  * At botDesc/botRise and their fresh children, `R` enters (children `G = R`, `a = R − G`). The
    "one child spans both cuts" case (sparse bottom, `a − π < R_child`) appears here.
  * The bounds need `R/c` exponent facts, e.g. `h+2 ≤ g ≤ h+6`, which today come from
    `omega7_bounds`/`omega7_lt_d`. These are omega lemmas on the schedule, proven for all d as now.
  * **This is the only place where a finite-role invariant might fail to exist.** Stage 0 must
    check it.
* **(I4) Grain.** Every `G_y(t)` and `π_y(t)/2` is a multiple of `γ(level, t)`, and
  `a/γ ≤ 2^43`. Then `geom` follows from a single generic lemma, which replaces the four
  templates. The lemma picks `n = γ` or `2γ` so that `m = a/n ∈ (2^42, 2^43]`.
  * Interior grains nest correctly: children's `G` grain at t is `c(i+1,t)/2^K`, which is 64×
    coarser than `c(i+1,t+1)/2^K`.
  * **The window issue (new finding).** `a/c` straddles 1 (`a ≤ η c`, η > 1; measured
    1.000032), but `m = a·2^43/c` must be ≤ 2^43. Two fixes:
    * (a) choose `γ = c/2^42` and use `n = c/2^43` if a ≤ c, `n = c/2^42` if a > c;
    * (b) add the design constraint a ≤ c.

    Bottom nodes have `a ≪ c` possibly, so their grain must be tied to `R`, not `c` (today's
    `botDesc` template `8192R+8190`).

**Mechanism for "all d".** Every inequality is homogeneous in c (divide by c). c-ratios between
parent and child and between t and t±1 are fixed powers of 2. Hence each transition is one
rational linear inequality, valid for all d, plus exponent side conditions from the schedule
(`omega`). This is exactly how `NodeShape.facts` works today (`Wires31:142–180`), except that
the per-node data is `G/c ∈ [0,g*]` rather than `= closed form`. `decide` is not needed. The
growing class count is irrelevant because the invariant quantifies over all bags.

### 3.4 Line estimate for the table (Stage 2)

| part | lines |
|---|---|
| definitions, (L1)–(L3) | 600–900 |
| (I1)/(I2) role-transition invariant | 700–1100 |
| (I3) bottom | 400–800 |
| (I4) grain + generic geometry | 400–700 |
| `FlowFacts` assembly, t = 0/1, final | 200–300 |
| **total** | **2.3–3.8k** |

`FlowTable`, `FlowSizes7`, `Wires31`, `NodeGeom` (≈1040 lines) are deleted or kept only for
the regression instance.

## 4. Staged plan

Every stage ends with `lake build` (full) plus `lake build AKS.Bounds.Chvatal1830Axioms`, and a
guard that only `propext`, `Classical.choice`, `Quot.sound` appear and no `sorry`.

**Stage 0: design freeze (Python only, 1 agent, no Lean).**
* Write `d2lean.py`, which implements §3.1 *literally* in ℕ: floors, rounding to γ, the
  sparse-bottom clipping.
* Run it on (6,12,6) and (6,10,6) for d = 14…60. Check:
  * integrality, b ≥ 0, conservation;
  * `a ≥ π`, `a ≤ ηc`;
  * `residAt ≤ rT c` with the exact `residAt` of §2.1;
  * geometry `NodeGeomV` for every big sender;
  * `top G = 0`, `final`.
* **Extract and check by interval arithmetic** that a finite role-indexed box invariant on
  `(gL/c, gH/c, a/c)` is closed under all role transitions. Bottom roles may carry `R/c`
  exponent parameters, as in today's `(g,h)`.
* Also check that the (6,10,6) schedule meets: `α(tf) = ω(tf)` for every d, with `tf` given in
  closed form per `d mod 3`.
* **Gate G0:** an inductive invariant exists and is written down. Otherwise **no-go**.

**Stage 1: interface + regression (uniform table, (6,12,6), headline stays 1419).**
* 1-pre (1 agent, first): the `FlowTableB`/`FlowFacts`/`NodeGeomV`/`NodeSpec bds` definitions
  file. 150–250 lines.
* Then in parallel:
  * **1a** `WireFlow`/`ExecPlacement`/`FringeSendReal`/`RealNetwork`, per bag with offsets:
    400–600.
  * **1b** `NodeSpec`/`NodeKeys`/`PackSpec(2)`/`FlipSpec`/`PackNodeSpec2`/`TwoRoundHyp`/
    `TwoRoundProof`/`RealNets.packNodeSpec`, with `bds` and `2f ≤ m`: 200–350.
  * **1c** generic deficit + `Lemma41Real` per bag, and `BadSendReal` prefix-window: 450–700.
* Then 1 agent, sequential:
  * **1d** uniform instance `flowFacts7 : FlowFacts (uniformB d hd) capacity (d−6) 1 slackCoeff …`
    from existing lemmas: 300–500;
  * **1e** `KernelSetup`/`BadSendField`/`FringeSendField`/`RealKernel`/`RealNets`/
    `RealInduction`/`RealBlocks`/`RealSorter` over `FlowFacts`: 400–600.
* **Total 1.9–3.0k.** Checkpoint C1: green, 1419 unchanged. This de-risks all downstream
  threading with zero numeric risk.

**Stage 2: D2 table at (6,12,6) constants (headline still 1419).**
* 2a: definitions + (L1)–(L3) + `FlowTableB` fields (1 agent).
* Then in parallel: 2b (I1/I2), 2c (I3 bottom), 2d (I4 grain/geometry).
* Then 2e: assemble `FlowFacts` with `rT = g*` (+ rounding); swap the instance in `RealSorter`.
* **2.3–3.8k.** Checkpoint C2: green, 1419. R1 at (6,12,6) is feasible at L42 (`feas_L42.out`).
  This proves the table is right before any constant moves.
* Write 2b–2d against a constants record `(A ν : ℚ)` with hypotheses, so that Stage 3
  re-instantiates them instead of re-proving.

**Stage 3: switch to (6,10,6).**
* `Schedule10`: α\* = (6t−6d+23)/10, ω\* = (6t+10)/16, `tf` by `d mod 3` (or the period
  omega finds); exponent lemmas over 2^e, not 64^e. 300–500.
* Constants: `capacity`, `invMu = (4.4)` value, `invDelta`, `siblingFactor`,
  `rT`, `η`, `cond42/44/45`, `lemma32` cap 2^28, `capacity_two_levels`, `sibling_sum_le`,
  `childrenR_scale`. 200–350.
* Table re-instantiation (I1–I4 numerals): 100–250.
* `RealBlocks`/`FinalSorts` with λ(d) and block ≤ 2^42; `DepthSkeleton`/`RealSorter` with
  `totalDepth`; headline ≈ `(3784/3) lg n − C`, i.e. 1261.3. 150–300.
* **0.75–1.4k**, mostly sequential (Schedule first). Checkpoint C3: green, new headline + guard.

**Totals.** Stages 1+2+3 ≈ **5.0–8.2k lines** (centre ≈ 6k), against 2.5–4k in SLACKFREE §6.

**Parallelism.**
* 1a/1b/1c run in parallel after 1-pre.
* 2b/2c/2d run in parallel after 2a.
* Stage 3 can start its `Schedule10` and constants work during Stage 2, in a separate module,
  not wired in.
* Sequential agents are needed for 1-pre, 1d/1e, 2a, 2e and the Stage 3 wiring.

### Separator side (unequal blocks): the complete list

* `NodeSpec.blockBounds` is replaced by an arbitrary boundary set `bds`.
* `packSpec2_high/low` and `packSpec_high/low` are restated for row-multiple boundaries. The
  proof already works for any `p = i·n` (`PackSpec2:118–122`, flip via `packSpec2_low:209`).
* `physicalPack2Net` and its row partition need **no change**.
  * The network is the same sort–scramble–sort on m×n.
  * The row partition `f | b_1 … b_64 | f` is only interpretive.
  * B2 holds for *every* row threshold `1 ≤ i ≤ m` (`HasPackSemanticPropertyB2`).
  * F2 refers only to `f`.
* `NodeGeom` becomes `NodeGeomV` with `m = 2f + Σ b_j`. `nodeGood_geom` and
  `TwoRoundSeparatorExists._hshape` change to `2f ≤ m`. `TwoRoundProof` uses
  `ofShape … (m−2f) f 1`.
* The bulk/fringe existence lemmas (`Bulk2*`, `F2*`) use only `(m, n, f)` and the window. **No
  existence lemma assumes equal b.** The only `b` use is `hshape ⇒ f ≤ m`
  (`MatrixBridge:317`).
* The root separator (`nodeGood_root`) stays uniform.

## 5. Risks

* **R1 (high): bottom invariant (I3).** Sparse-bottom clipping makes `G` of a fresh child
  depend on `R − (a−π)`. If no finite role box closes, the proof needs an unbounded
  exponent-parametrized case analysis. That is like today's `botDesc (g,h)` but with
  inequalities, and could double (I3). Mitigated by Gate G0.
* **R2 (medium): geometry and grain (I4).**
  * `a > c` breaks `m ≤ 2^43` with grain c/2^43 (found here, not in SLACKFREE).
  * Bottom grains must follow `R`.
  * Rounding perturbs `resid` by O(64γ) ≈ 2^-32 c ≈ 0.06 μ, which is fine but must be carried.
* **R3 (medium): (6,10,6) schedule.** `tf ≈ 8d/3 − 13…15` depends on `d mod 3`. `α(tf) = ω(tf)`
  must hold for **all** d, and parity rounding with ÷10 and ÷16 could overshoot. `compressed.py`
  only saw d ≤ 24. This is checked in Stage 0, and `omega` proves it in Lean.
  * The G-based table no longer needs `capacity_meet7_div`, since `a = R` at λ comes from
    `G = 0` at tops.
  * `real_purity` needs `μδ·c(λ,tf) < 1`, which holds since `c ≤ 2^36`.
* **R4 (low–medium): elaboration cost.** Per-bag `∑ j : Fin 64` with prefix filters in
  `omega`/`linarith`-heavy proofs. Keep prefix sums as `ℕ`-valued functions with explicit
  monotonicity lemmas.
* **R5 (low): the D2 versus P choice.** At L42 with the certified ε_B = 1/59e6, D2's residual
  2.1 μ (against P's 1.97 μ) leaves ≥ 5 μ margin in (4.2). The slope 1261.3 is unchanged,
  since the stage depth 2838 and window L42 are set by the fringe floor.
* **R6: no gain without Stage 3.** (6,12,6) gives 1419 under R1. All value arrives at C3, so
  C1 and C2 are pure risk-reduction checkpoints.
* **Not a risk:**
  * the separator side (§4 list, ≈ 200–350 lines);
  * Lemma 4.1/4.2 generalization: the key intervals stay uniform, and only the cell windows and
    per-child counts change.
