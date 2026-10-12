# Gate G0 (Stage 0): freezing the D2 design at (6,10,6) and (6,12,6)

2026-10-11. Python with exact integers and Fractions only. No Lean was edited and nothing was
committed. Scripts and outputs are in this folder:
* `d2lean.py` → `d2lean_6106.out`, `d2lean_6126.out`
* `invariant.py` → `invariant_6106.out`, `invariant_6126.out`
* `schedule.py` → `schedule.out`

## VERDICT: GO, with one change to the rule

The table checks pass at both triples, and a finite-role invariant exists and closes.
* **The rule.** The rounded D2 rule below is integral and conserves wires. It satisfies every
  `FlowFacts` field at both triples for d = 14…60, with zero violations (§2).
* **The invariant.** A finite, scale-free invariant exists and is inductive. Its parts:
  * one state bound, plus one sign condition per bag;
  * one a-interval per schedule signature (39 classes at (6,10,6), 24 at (6,12,6));
  * exponent side conditions, which Lean can discharge by `omega`.

  Every transition is one linear inequality over ℚ, and all of them are checked exactly
  (§3). The schedule signatures were enumerated for d ≤ 300; every class has appeared by d = 19.
* **The real margin.** Condition (4.2) at (6,10,6) with ε_B = 1/59e6 holds with real margin
  **2.1356**. That is the minimum over all actual integer nodes, the same for every d. Using the
  uniform constants that Lean would carry (rT, η) the margin is **2.1336**.
* **The headline.** The (6,10,6) schedule meets for every d. tf and λ have closed forms with
  period 6 in d. The result is **D(n) ≤ (3784/3)·lg n − 24433 ≈ 1261.33·lg n − 24433** (§4).

**INTERFACE §3.1 has to change: "round lo/hi to the grain, which changes only lo/hi" cannot
work.**
* Conservation forces hi − lo = a − π, so lo and hi cannot be rounded independently.
* For a sender x at (i,t) whose 64 children are big at t+1, each block must be ≡ 0 mod n_child,
  and n_child = 16·n_x. Hence a_x − π_x ≡ 0 mod 16·n_x. Pushed to the parent, this requirement
  grows by 16× per level, so no fixed grain can satisfy it.
* This is exactly why exact D2 fails the geometry check: 399 of 575 big senders fail at
  (6,12,6), d = 24 (`--nogrid`).
* **The fix is to shift lo, set hi = lo + a − π′, and give π a small upward adjustment:**
  π′ = π₀ + ((a − π₀) mod Γ). This breaks the escalation, because the requirement on each bag
  is now just a ≡ 0 mod γ(own level), and that is supplied by the parent's grain.
* The cost: π′ ∈ [π₀, π₀ + Γ). Relative to π₀ the adjustment is ≤ 2^-13 at (6,10,6) and
  ≤ 2^-9 at (6,12,6).

## 1. The frozen rule (complete enough for a Lean `def`)

**Parameters.** k = 2^x, A = 2^y, ν = 2^-z. Capacity c(i,t) = 64^d·A^i·ν^t/(Aνk), always a power
of 2. Grain γ(l,t) := 2^max(0, v₂(c(l,t)) − 39), and Γ(i,t) := γ(i+1, t+1).

**State.** st : ℕ → KBag → ℕ × ℕ, written (gL, gH), with G := gL + gH.

**At t = 0.** The root has (0,0) and every other bag has (0, R_l), where R_l = 64^(d−l). The root
sends 64^(d−1) to each child with π = 0, so every level-1 bag ends with (0,0).

**Step t → t+1** (1 ≤ t < tf), for each active sender x at level i:

```
S_j  := Σ_{q<j} G(child q)                  -- ℕ prefix sums, S_64 = S
a    := S − G(x)                            -- R_i − G(x) at a leaf
role := topDesc | topRise | mid | botDesc | botRise      -- from α(t), α(t+1), ω(t), ω(t+1)
π′   := if botRise then a
        else if topDesc then 0
        else π₀ + ((a − π₀) mod Γ)
        -- π₀ = (Aνk−1)c/(A²k²) for mid and botDesc, π₀ = νc/(Ak) for topRise
lo   := Γ · ((gL + π′/2) / Γ)              -- ℕ floor division
hi   := lo + (a − π′)
for every j < 64:
  cl_j   := min(S_{j+1}, lo) − min(S_j, lo)
  ch_j   := max(S_{j+1}, hi) − max(S_j, hi)
  down_j := G(child j) − cl_j − ch_j        -- = |[S_j, S_{j+1}) ∩ [lo, hi)|
  st(child j) := (cl_j, ch_j)
st(x) := (lo, S − hi)                       -- botRise: (gL, gH + a); in both cases G(x) += π′
up(x) := π′
```

All other bags are unchanged.

**Geometry instance.** For a sender with a > 2^63 and Σ down > 0:
* n := 2^(⌈lg a⌉ − 43), which is c/2^43 when a ≤ c and c/2^42 when c < a ≤ 2c (fix (a));
* m = a/n ∈ (2^42, 2^43];
* f = π′/(2n);
* b_j = down_j / n.

Lean needs only a ≤ 2c and a > 2^63 here. Because n is chosen from a, a bottom sender with a ≪ c
simply gets a smaller n. No R-tied grain is needed.

**Generic lemmas (no numerics).**
* (L1) Σ down = a − π′, b ≥ 0 iff lo ≤ hi, and Σ_j (cl_j + ch_j) = G + π′.
* cl_j ≤ lo, and ch_j ≤ S − hi.
* If no child "spans" (cl_j > 0 and ch_j > 0 for the same j), then min(cl_j, ch_j) = 0.
* lo ≤ gL + π′/2, and S − hi ≤ gH + π′/2 + Γ.
* residAt_j ≤ (lo − π′/2)⁺ + (S − hi − π′/2)⁺ ≤ max(gL, gH) + Γ, using min(gL, gH) = 0.
* (L2) Inactive bags hold no wires. Hence for i = ω(t) all children's subtrees are empty and
  **a = R_i − G(x)**.

## 2. Checks on the exact tables, d = 14…60, both triples (`d2lean_*.out`)

**Calibration.**
* Design U reproduces Lean `allocation` on every sender (0 mismatches).
* It also reproduces the R0 (4.2) margin of 1.0670 (feas.out: 1.07) and slackCoeff = 2.8878e-8.
* The schedule's general envelopes equal Lean `alpha7`/`omega7`, with tf = 3d − 20, for d ≤ 300
  (`schedule.out`).
* `--nogrid` reproduces `compressed.py` D2: a/c 1.000002 and G/c 4.729e-10.

**Rounded D2, all 47 values of d at each triple.** Zero violations of:
* integrality, b_j ≥ 0, π even, a ≥ π′;
* per-sender conservation, the global wire count = 64^d at every stage, and G update = π′;
* lo and hi in range, 64 children per sender;
* NodeGeomV for every big sender (n | a, n | b_j, 4n | π′, f = 0 or f ≥ 131040 and even,
  m ∈ (2^42, 2^43]);
* the final facts (α(tf) = ω(tf), G = 0 above λ, a = R_λ at λ) and top G = 0.

The one flag, `big_a_gt_c`, is informational: those senders have c < a ≤ 2c and pass the
geometry check through fix (a).

| quantity | (6,10,6) | (6,12,6) |
|---|---|---|
| max a/c (data) / η proved (formula) | 1.000032425 / 1.000153768 | 1.000244141 / 1.001955491 |
| max G/c (data) / g\* | 7.9399e-9 / 7.9424e-9 | 4.7476e-10 / 4.7571e-10 |
| max residAt/c (data) / rT = g\* + γ | 7.9426e-9 / 7.9715e-9 (= 2.1435 μ) | 5.8662e-10 / 5.9212e-10 (= 0.636 μ) |
| (4.2) margin, worst actual node / with (rT, η) | **2.1356** (t=13, i=5, mid) / **2.1336** | 2.7356 / 2.7306 (R0: 1.067) |
| f range of big senders | [523776, 1.098e12] | [131052, 1.074e9] |

**Notes.**
* f > 8.5e9 occurs at (6,10,6) botDesc nodes with a/c ≈ 2^-20…2^-14. Chvátal's U table has the
  same values. Lean already covers this case: `TwoRoundProof` splits on `f < 8500000000`, and
  `Lemma62Round` gives ε = 1/86e6 for f ≥ 8.5e9 with f ≤ m.
* The cond (4.2) definition and constants are those of `feas.py`, i.e. the margin is
  room/(ε_B·a):
  * μ = (1 − 2^-10)·min((4.3),(4.4)) = 3.7189e-9, binding on (4.4);
  * δ from (4.5) = 7.2897e-10;
  * ε_F = 1/86e6.

## 3. The finite-role invariant (`invariant.py`)

### Ratios used

Every quantity below is divided by the c of its own bag. These ratios are fixed:
* c(i+1, t−1)/c(i,t) = A/ν;
* c(i, t−2)/c(i,t) = ν^-2;
* c(i−1, t−1)/c(i,t) = 1/(Aν);
* R_i/c(i,t) = 2^e with **e = (x+y−z) − (x+y)·i + z·t**. This is the only non-homogeneous datum,
  and it is an exponent.

The constants are p = (Aνk−1)/(A²k²), p_T = ν/(Ak) and γ = Γ/c = Aν/2^39.

### Roles

The signature of a sender x at (i,t) is
(role x@t, role x@t−2, role children@t−1, role parent@t−1).

The roles are root, topDesc, topRise, mid, botDesc, botRise, above and below. For bottom
classes the signature also carries e. Enumerated over all senders for d = 14…300:
* **39 classes at (6,10,6), 24 at (6,12,6)**;
* each class has appeared by d = 19;
* the period in t is 16 at the bottom.

So the set is finite and independent of d. The classes:
* **Top:** topDesc/topRise at t, combined with {root, topDesc, topRise, mid, botDesc} at t−2
  (12 classes).
* **Mid:** mid at t, combined with {mid, botDesc}² for (x@t−2, children@t−1) and parent
  {mid, topRise} (6 classes).
* **Bottom with e:** at (6,10,6):
  * botDesc after botDesc, e ∈ {0,−2,−4,−6,−8};
  * botDesc after botRise, e ∈ {−10,…,−18};
  * botDesc fresh (x below the bottom at t−2), e = −20;
  * botRise, e ∈ {−22,…,−30};
  * plus two early classes (t ≤ 2) and topRise at t = 1.

### Invariant (J)

For every t ≥ 1 and every bag y with y.l ≡ t (mod 2) and α(t) < y.l ≤ ω(t):
* min(gL, gH) = 0;
* h := max(gL, gH) ≤ g\*·c(y.l, t).

Bags at y.l ≤ α(t) have G = 0.

**Step.** h_y(t) ≤ h_p(t−1) + π′_p/2 + Γ_p and π′_p < π₀_p + Γ_p. This gives two inequalities:
* **(J-mid)** g\*·Aν ≥ g\* + p/2 + (3/2)γ (parent is mid or botDesc). g\* is *defined* by this
  with equality: g\* = (p/2 + 3γ/2)/(Aν − 1) = 2729/(10·2^35) at (6,10,6).
* **(J-top)** g\*·Aν ≥ p_T/2 + (3/2)γ (parent is topRise with h_p = 0). Slack 7.8e-9 ✓.

Other parents:
* A topDesc parent gives θ = 0.
* A parent that is inactive at t−1 means y is top, so G = 0.
* A botRise parent at t−1 is impossible for an active y.

The sparse-bottom case, where a child lies wholly below lo, is covered because cl ≤ lo.

### a-intervals (A), one per class, from exact identities

| formula | applies to |
|---|---|
| **(R−G)** a = R_i − G(x), so a/c ∈ [2^e − g, 2^e] | i = ω(t), or children at t−1 are botRise or below |
| **(C1)** a = [G_x(t−2) + π′_x(t−2)] (when x cut at t−2) + Σ_l π′_l(t−1) − G_x(t) | all other classes |

Under C1, a/c ∈ [(1 − 2^-20) − g\*, (g\* + p + γ)ν^-2 + 64(p + γ)A/ν] = [0.99999899, 1.000153768]
at (6,10,6).

### Checks per class

For senders that send blocks, these must hold:
* **a ≥ π′:** a_lo ≥ π₀ + Γ.
* **(NS) no spanning:** a_lo − π₀ − Γ ≥ max child G. The max child G is
  (g\* + p + γ)·A/ν = 0.0161 for C1 and 2^(e−6) for R−G.
* **a ≤ η·c:** with η = max a_hi.

**All 39 and all 24 classes pass, with 0 failures.** The binding bottom inequality, for botDesc,
is 2^e·(63/64) ≥ g\* + p + γ = 2.4615e-7, i.e. e ≥ −21. The schedule gives e ≥ −20, so that is
1 bit of exponent slack, a factor of 3.8.

### Residual (R)

residAt ≤ h + Γ ≤ (g\* + γ)·c = rT·c.

### Grain (I4)

The induction:
* every child's G(t) is ≡ 0 mod Γ_x(t). Each is one of:
  * θ from x's cut at t−2, a multiple of 4096·Γ_x(t);
  * π′ ≡ 0 mod γ;
  * R_{i+1}, which needs e(i+1, t+1) ≥ −39. That follows from botDesc ⇒ e ≥ −20;
* gL, gH ≡ 0 mod γ(own level), because the parent's lo is ≡ 0 mod Γ_parent;
* hence a ≡ 0 mod γ(i,t);
* hence π′ − π₀ ≡ 0 mod γ;
* hence n = 2^(⌈lg a⌉−43) divides γ whenever a ≤ 16c. With a > 2^63 ⇒ c > 2^62, γ ≥ 2^23.

This is checked through the geometry check, and the reasoning is exponent-only.

### Exponent side conditions for `omega`

These are the analogues of `omega7_*`. At (6,10,6), e = 10 − 16i + 6t:
* (E1) i = ω(t) ⇒ −31 ≤ e ≤ 0.
* (E2) botDesc ⇒ e ≥ −20 (needs ≥ −21). botRise ⇒ e ≤ −22.
* (E3) i < ω(t) ⇒ i + 1 ≤ ω(t−1) (children active), and x was not "below" at t−2.
* (E4) α and ω move by ±1 per step and parity holds, so the role transitions are the 39 listed.

(6,12,6) uses e = 12 − 18i + 6t with e ∈ {0, −12} at botDesc and −24 at botRise.

### Data check

159,679 senders at (6,10,6) and 166,970 at (6,12,6) all lie in their class's formula interval.
Also, with 0 violations:
* min(gL, gH) = 0 for every non-top bag;
* h ≤ g\*·c and residAt ≤ rT·c;
* no spanning child;
* top G = 0.

## 4. Schedule and depth at (6,10,6) (`schedule.out`)

**Envelopes.**
* α(t) = ceilParity(max(0, ⌈(6t − 6d + 23)/10⌉), t)
* ω(t) = ceilParity(⌈(6t + 10)/16⌉, t)
* tf = the first t ≥ 2 with α(t) ≥ ω(t)

For d = 14…300, α(tf) = ω(tf) always (no overshoot), and α < ω on 2 ≤ t < tf. **The period is
6 in d, not 3**, because d mod 3 alone leaves two values per class.

| d mod 6 | 3·tf − 8d | λ = meet level | final block (= 64 children) | c(λ,tf) | totalDepth = (3784/3)·6d − c₁ |
|---|---|---|---|---|---|
| 0 | −45 | d−5 | 2^36 (T = 666) | 2^30 | c₁ = 38422 |
| 1 | −41 | d−4 | 2^30 (T = 465) | 2^32 | 34839 |
| 2 | −40 | d−4 | 2^30 | 2^30 | 33893 |
| 3 | −39 | d−4 | 2^30 | 2^28 | 32947 |
| 4 | −38 | d−4 | 2^30 | 2^26 | **32001** (worst) |
| 5 | −46 | d−5 | 2^36 | 2^32 | 39368 |

**Inputs.**
* totalDepth = 6320 (root) + (tf − 1)·2838 + T(lg finalBlock), the same skeleton as
  `DepthSkeleton`, where ordinary rounds = tf − 1.
* The final block is ≤ 2^36, below the 2^42 limit.
* Purity holds: μδ·c(λ,tf) ≤ 1.2e-8 < 1.

**Result.**
* totalDepth(d) ≤ (3784/3)·6d − 32001.
* With lg n > 6(d−1), **D(n) ≤ (3784/3)·lg n − 24433**, i.e. C = 1261.33 and c₀ = 24433.
* For comparison, (6,12,6) is 1419·lg n − 43861.
* In Lean either keep the rational coefficient 3784/3, or state 1262·lg n − 24433, which is
  weaker but valid.

**New Schedule10 constants:**
* tf = (8d + κ_{d mod 6})/3 with κ = (−45, −41, −40, −39, −38, −46);
* λ = d − 5 when d ≡ 0 or 5 (mod 6), and d − 4 otherwise.

**Assumption.** The root depth 6320 and stage depth 2838 = 3·T(43) are carried over unchanged.

## 5. Risks (updated)

* **R1 bottom invariant: retired.** No spanning child ever occurs; sparse cuts happen only at
  botDesc with t mod 16 ∈ {3, 6}, and cl ≤ lo covers them. The bottom needs only (R−G) plus the
  exponent bounds (E1) and (E2): a finite set of e values, not an unbounded case split.
* **R2 grain: changed.** The rounding rule in INTERFACE is unsound (conservation). The frozen
  rule adjusts π upward.
  * Lean must take up = π′ ∈ [π₀, π₀ + Γ). This is fine for `fringe` (upFrac·c ≤ π′).
  * Every Lean use of an *upper* bound or exact value of π needs slack ≥ Γ/π₀:
    * relative ≤ 2^-13 at (6,10,6) and ≤ 2^-9 at (6,12,6);
    * this touches the (4.4)/(4.5) fringe-stranger terms, `StageKernel` literals, and a ≤ ηc
      with η = 1.00015 / 1.00196.
  * Each is a negligible numeric change, but it must be threaded through.
  * Alternative: halve Γ (shift 40). Do not adjust π downward, because that breaks the fringe
    floor.
* **R3 schedule: resolved numerically** (period 6, meets for d ≤ 300). Lean needs a mod-6 `omega`
  proof of meet, apart and (E1)–(E4).
* **R4 elaboration cost: unchanged.** About 39 role classes against 5 `NodeShape`s today, but
  each is one `linarith` instance over the same template.
* **R5 (new, low): the margin is from formulas, not proved.** The 2.13 margin uses the
  ε_B/μ/δ conventions of feas.py; StageKernel's exact literals were not re-derived here.
* **R6 (new, low): this is an exact enumeration, not a Lean proof.** Class finiteness and
  d-independence are established up to d = 300 (signatures) and d = 60 (tables); the all-d
  claim rests on (E1)–(E4) being `omega` facts. The identities C1 and R−G are generic lemmas;
  the data are consistent with them (every record lies inside its interval) but they were not
  machine-proved.
