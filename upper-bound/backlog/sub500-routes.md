# Routes below 500 from the 789.75 endpoint

Claude (Opus 5.5), 2026-10-20. Planning note for UB-32 to UB-38. The numbers below are model
estimates, extrapolated from the 789.75 point (`../best/notes/sub800/R1-PROOF.md`,
`../best/notes/sub800/r1_point.out`, `../best/notes/sub800/cert_walk.out`). None is a result.

## Where 789.75 comes from

The accepted network is Chvátal's tree at `(k, A, ν) = (2^x, 2^y, 2^-z) = (16, 32, 1/8)`, with
design P as the flow table. Every large bag runs the padded two-round separator: two scrambles and
three Batcher column sorts of height `2^q`, `q = 26`. So

```text
coefficient = (sorts per stage) · S(q) · (stages per bit),   S(q) = q(q+1)/2
            = 3 · 351 · (x+y)/(xz) = 3 · 351 · 9/12 = 789.75
```

The row exponent `q` is the larger of two floors.

* **Fringe floor.** `m ≈ 2(f+1)/p` rows, where `p = (Aνk−1)/(A²k²) = 63/2^18` is the up-flow per unit
  capacity. With `f = 7934` this gives `log₂ m = 25.98`. In general `q_fringe ≈ x+y+z + log₂(2(f+1))`.
* **Bulk floor.** The walk bound must reach `ε_B`. Between `2^25.6` and `2^26` its value scales
  like `m^-0.75` (`cert_walk.out`). At `ε_B = 1/105000` the floor is `q_bulk ≈ 25.3`.

`ε_B` is whatever is left of the (4.2′) budget, `Aν·μ = 4μ`. The base, sibling, δ and reserve terms
take `1.45μ`, and the design-P residual `r* = 15/2^19` takes `1.91μ`. That leaves
`ε_B·η ≈ 2.55μ − r* ≈ 0.64μ`. **The residual uses most of the budget, so `ε_B` reacts strongly to
`μ` and `r*`:**

| change | `ε_B` budget | `q_bulk` (walk slope 0.75) |
|---|---:|---:|
| none (μ = 1.50e-5) | 9.6e-6 | 25.3 |
| `μ × 2` (e.g. `δ_F = 1/4`) | 4.8e-5 | 22.2 |
| `r* = 0` (two-sided invariant) | 3.8e-5 | 22.7 |

At `x+y+z = 12`, the fringe floor drops to 24 at `f = 2000`, 22 at `f = 500`, and 19.7 at `f = 100`.

## Gates below 500

| sorts / stage | `q` | coefficient |
|---:|---:|---:|
| 3 | 26 | 789.75 |
| 3 | 22 | 569.25 |
| 3 | 21 | 519.75 |
| **3** | **20** | **472.5** |
| 2 | 26 | 526.5 |
| **2** | **25** | **487.5** |
| 2 | 24 | 450 |

At the same schedule there are two ways below 500:
* keep three sorts and reach `q ≤ 20`, which needs both floors near 20;
* drop to two sorts per stage and reach `q ≤ 25`.

Two sorts alone, at `q = 26`, stop at 526.5.

## Ideas

### UB-32 (P1): two column sorts per stage

Replace the third column sort with a short repair, or drop it. If the repair has depth `R`, the
coefficient is `(2·S(q) + R)·3/4`. That is below 500 only for `q ≤ 25` and `R < 17`, or for `q ≤ 24`
and `R < 66`. So this idea must be combined with a one-step drop in `q`, which UB-33 or UB-34 could
provide.

The question to settle first is which guarantees the proof actually draws from the third sort:
* the two-sided cut bounds of `paddedPack2Net_all_cut_bounds` (Property B in both directions);
* the fringe escapes, `fHigh`/`fLow`.

**Is a one-sided version enough for design P?** Its residual is already one-sided.

**Known obstruction:** `archive/roadmap-700-200.md` §2. L1 (mass) control alone cannot certify a
narrow-band repair. The walk bound controls each threshold summed over columns, not per-column tails,
so the same obstruction applies until a per-column tail statement is proved.

First deliverable: a list of the third sort's uses in `PaddedSeparator`/`BaselineFringeD` and in
the R1 node specification, and for each use either a weaker property that suffices or a
counterexample.

### UB-33 (P1): raise μ, or remove `r*`

The (4.2′) budget is dominated by `r*`. Two levers:

* **Larger `δ_F`.** `μ ≈ ½·δ_F·p`, so going from `δ_F = 1/8` to `1/4` doubles `μ` and multiplies the
  `ε_B` budget by about 5 (q_bulk 25.3 → 22.2).
  * Cost: the fringe must certify escapes for `jmax = δ_F·f·n` real keys. The per-E route
    (`F2D*`, `gen_fringe.py`) takes `δ` as a parameter, so this is a generator run before it is
    any proof work.
* **Remove the residual.** A flow table or invariant without the one-sided `r*`. Route R2 of
  `../experiments/slackfree/SLACKFREE.md` (767) is the known version. It needs the two-sided
  invariant of UB-24.

The bulk floor alone does not move the coefficient while the fringe floor stays at 26. So UB-33 only
pays off together with UB-34 or UB-32.

First deliverable: rerun `gen_fringe.py` at `δ_F ∈ {1/6, 1/4, 1/3}` and record the smallest
certifiable `f` and `J` for each. Then price `q = max(q_bulk, q_fringe)`.

### UB-34 (P1): take the fringe off the row count

`m ≈ 2(f+1)/p` holds only because the fringe classes are protected inside the same rectangle as the
bulk. Two candidate fixes:
* handle the `π/2` extreme positions with a separate exact sort or merge;
* give the fringe its own small rectangle.

Either would leave `q` set by the bulk floor alone. Combined with UB-33 (`q_bulk ≈ 22`) this gives
`569` with three sorts and `≈ 380` with two.

* Cost: the extra fringe network runs in parallel or in series with the separator, and its depth must
  stay below the saving.
* Possible lead: the fringe certificates already show that `f ≈ 100–500` behaves well per round.

First deliverable: a depth and contract sketch of a split node:
* bulk separator on `2^q` rows;
* fringe network on the top and bottom `(f+1)·n` positions;
* proof of how the two compose in the (4.2′)/(4.4) accounting.

### UB-35 (P1): generic failure budgets and root separator (infrastructure)

* The failure budgets (`1/100`, `1/1000`, `1/10000`) in `SepExists` become parameters, with the
  condition that each pair sums to less than `1/2`.
* The root separator (`2^42` rows, `ε = 1/59·10⁶`, depth 2709) becomes a parameter of `R1Point`.

This affects only the constant term and the generators' freedom, but it is about two hours of work.
It is the remaining easy part of the Lean genericity (tier 1 is done: `R1Scal`, `R1Point`,
`R1GeomGen`).

### UB-36 (P2): generic schedule `(x, y, z)` with per-point design-P checks

The R1 layer still fixes `(16, 32, 1/8)`: the constants 63, 64, 2^19, 4094–4104, and the bottom
ratios by `t mod 6`. Instead of a symbolic proof, state the point-specific facts as finite residue
checks (closed by `decide`). The invariants (I1)–(I4) of R1-PROOF §2 become lemmas over the
exponents with checked side conditions.

This pays off only once UB-32 to UB-34 change the trade-off between `x+y+z` (which sets rows) and
`(x+y)/(xz)` (stages per bit). Run UB-37 first.

### UB-37 (P1): re-price sweep over the full model

A sweep over `(x, y, z, δ_F, f-classes, q, sorts per stage)` with the formulas above and the real
certificate generators. It should report the best point under each hypothetical:
* status quo;
* `δ_F = 1/4`;
* `r* = 0`;
* split fringe;
* two sorts.

This replaces the per-assumption estimates above with one consistent table and tells us which of
UB-32 to UB-34 to fund. The earlier scan (sub800 README, "Model scan") covered only the status quo
and `δ_F ∈ {128/4095, 1/8}`.

First deliverable: a `notes/` script and table, with every entry labelled `model`.

### UB-38 (P2): run-aware first sort and stage fusion at the R1 node

* **Run-aware first sort.** A bag's input is a few sorted runs: one block from the parent and up to
  16 from the children. UB-13 priced a run-aware first sort at most −16% of one sort. At R1 that is
  `≈ 0.16 · 351 · 3/4 ≈ 42` off the coefficient (`≈ 748`).
* **Stage fusion.** Overlap the last sort of stage `t` with the first sort of stage `t+1`. This is
  speculative, because the two rectangles group wires differently.

Both are modest. Keep them as add-ons to a route that already clears 500.

## Recommended order

1. UB-37, a cheap model sweep, together with the UB-33 generator runs at larger `δ_F`.
2. UB-32: which guarantees the third sort provides, at paper level.
3. UB-34: a contract sketch, if the sweep shows the fringe floor binding after UB-33.
4. UB-35 any time. UB-36 only once the sweep points away from `(4, 5, 3)`.

Below 200 needs a different architecture. Those ideas stay in UB-08/09 (high-arity sorters,
finite-M) and UB-25 to UB-28 (`sub200-structural-strategies.md`).
