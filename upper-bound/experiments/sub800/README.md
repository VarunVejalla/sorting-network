# UB-31: a sub-800 route without a new invariant (R1 at (16, 32, 1/8))

Ticket UB-31 · branch `ub-31-r1-sub800` · Claude (Opus 5.5) · 2026-10-19.

**Claim level.** A paper proof, R1-PROOF.md, reviewed twice in fresh contexts. The second review
found no blocking issue. The pieces have these statuses:
- **Exact rationals:** the scalar conditions (4.2)–(4.5).
- **Interval-certified:** the fringe (`fringe_cert_R1_f*.out`) and the walk-bound bulk
  (`cert_walk.py`, window [2^25.6, 2^26]).
- **Hand proofs:** the integer flow table and its invariants, and the separator geometry (§2 and §4).
- **Exact simulation (cross-check):** the flow table, d ≤ 22.
- **Single-review dependencies:** the walk bound (ROUND2) and the FRINGE-CERT §3 R2 tail.
- **Lean:** only W4.3 (`lean/NegAssoc.lean`) so far.

The accepted coefficient is still 1419.

## Why this route

The ≤ 800 candidates found so far (tapered at 792, see `../tapered-walk/README.md`; route R2 at
767) need a two-sided invariant: ancestral keys must be known to be extreme (SLACKFREE.md §3–4).
That is the open UB-24 gate. Route **R1** of `../slackfree/SLACKFREE.md` keeps Chvátal's invariant P
and changes only the flow table. Its price is the unavoidable one-sided residual
r* = (k−1)/(2A²k²) in (4.2).

Under P, R1 was 1261 at (6,10,6) with the old separator. Three changes compound:
- the walk-bound bulk (`../walk-bound/ROUND2.md`);
- a narrow row window with an arbitrary column count (the tapered recovery plan §2);
- δ_F = 1/8 in place of 128/4095. This is the same F2ROUND proof route at another parameter; its
  preconditions are checked by the certificate.

Together they reach **789.75** at (k, A, ν) = (16, 32, 1/8): rows < 2^26, a node of
3·S(26) = 1053 layers, and (x+y)/(xz) = 9/12 stages per bit.

Model scan (`reprice` variants run inline, 2026-10-19; certified-route fringe fits): R1 needs both
δ_F ≥ 1/8 and the narrow window. At δ_F = 128/4095 the best R1 point is 893. With a perfect fringe
it is 858, because the residual binds.

## The point (`r1_point.py` → `r1_point.out`; `fringe_cert_R1_f7934.out`)

| item | value | status |
|---|---|---|
| μ | (1−2^-10)·min((4.3), (4.4)) = 1.5006e-5, with (4.4) binding | exact |
| δ, ε_F | δ = 1.35e-6, J = ⌈1/ε_F⌉ = 186,215 | exact (4.5) |
| (4.2) | 0.99909, including r* = 1.907μ and a 0.1μ rounding reserve | exact |
| (4.3), (4.4), δkA | 0.983, 0.999, 6.9e-4 | exact |
| bulk | d(2^25.98) = 6.82e-6 ≤ ε_B = 1/105,000 (1.40×) | ROUND2 hand proof; interval-certified (`cert_walk.out`) |
| fringe | f = 7934, J = 190,000, δ_F = 1/8: ln(2P1) ≤ −3648, ln(2P2) ≤ −559 | interval-certified (per-E route) |
| depth | node 3·S(26) = 1053; exact Batcher for bags a ≤ 2^45 | arithmetic |
| coefficient | 1053 · 9/12 = **789.75** | conditional on the obligations below |

The (4.2) budget, in units of μ, against a total of Aν = 4:

| term | μ |
|---|---:|
| base | 1 |
| sibling | 0.332 |
| δ term | 0.022 |
| r* | 1.907 |
| rounding reserve | 0.1 |
| ε_B·η | 0.636 |

## The flow table: design P (`designP_sim.py`)

With deficit G_x = R_x − W_x (keys of x's range outside its subtree), design P sends
θ_end = π/2 + G_x − r*c to each end child and θ_int = (2r*c − G_x)/(k−2) to each interior child.

The exact real-valued hash-consed simulation uses Chvátal's α/ω schedule, at d = 10, 14 and 18 (tf up to
40); the integer rule runs to d = 22. It shows:
- no negative blocks;
- exact conservation;
- max G/c = 3.0518e-5 = g* = k·r*/(k−1);
- residual max_j(L_j⁺ + R_j⁺)/c equal to r* exactly;
- a/c ≤ 1.001680, below the η = 1.001831 that (4.2) uses.

The node classes are not type-closed: 24,013 at d = 20.

**Hand facts (to be written up).**
1. **Generalized Lemma 4.2.** Under P, the wrong keys in child block j are at most
   O_L + O_R + (k−1)Δ₁ + L_j⁺ + R_j⁺ + separator error, with L_j = T_{j−1} − π/2,
   R_j = π/2 + G_x − T_j and T the prefix sums of θ.
   - The proof uses only upper bounds: keys of range(l) held by x number at most G_l + Δ₁, by the
     deficit form of Lemma 4.1.
   - So no assumption about where the ancestral keys sit is needed. This is why R1 needs no new
     invariant.
2. **Residual.** If G_x ≤ g*·c, then max_j(L_j⁺ + R_j⁺) ≤ r*·c.
   - j = 1 and j = k give exactly r*c.
   - An interior j with both terms positive gives G − θ_int ≤ r*c, which is equivalent to G ≤ g*c.
   - Otherwise one term alone is at most the endpoint value.
3. **G stays at or below g*.**
   - End child: g′ = (p/2 + g − r*)/(Aν) ≤ g*, since g* is the fixed point.
   - Interior child: g′ = (2r* − g)/((k−2)Aν) ≤ g*.
   - Top nodes: G = 0.
   - The frontier roles (topRise with π = νc/(Ak), botDesc, botRise) are covered by the simulation
     in the simulation, and by hand in R1-PROOF.md §2.

**Integer table (`DESIGN=Pint`, `designP_int.out`).**

The rule:
- top senders (G = 0): s = 0;
- other senders: s = ⌈r*c⌉;
- θ_end = π/2 + G − s, and the interior total 2s − G is spread evenly, with the remainder going to
  the middle children first.

Every non-top sender lies at least two levels below the top, so c ≥ A²·2k² = 2^19 and
r*c = 15c/2^19 is an integer. The simulation (d = 10…22) shows:
- the integer residual equals r*c exactly (excess 0 wires);
- no negative blocks and exact conservation;
- G/c ≤ g*;
- a/c ≤ 1.001709, below η = 1.001831.

The 0.1μ rounding reserve is therefore needed only for the separator geometry below.

## Separator geometry (`designP_sim.py`, geometry line; R1-PROOF.md §4)

Large senders (a > 2^45) use the padded two-round separator `paddedPack2Net` of
`../tapered/BaselineFringe.lean`: an (m+1) × n rectangle with one partial dummy row and an
arbitrary column count. Its Property F counts real keys only, so there is no dummy-rank surcharge,
provided the protected (f+1)·n fits in the port.

- Fringe classes f are tried in order. For a class f, take n = ⌊π/(2(f+1))⌋.
- Require support μc ≤ δ_F·f·n, and live rows m = ⌈a/n⌉ − 1 ∈ [2^25.6, 2^26 − 1].
- The large topDesc root (π = 0, no outsiders) uses a bulk-only rectangle.

Every large sender (d = 14…22, all roles) fits, using only **two classes: f = 7934 and
f = 406,109**. Both are certified at J = 190,000 and δ_F = 1/8 (`fringe_cert_R1_f7934.out`,
`fringe_cert_R1_f406109.out`). The second is for sparse bottom senders (a/c ≈ 1/64). R1-PROOF.md
§4 gives the hand argument for all d.

The bulk is certified in interval arithmetic over the whole admitted window [2^25.6, 2^26]
(`cert_walk.py` → `cert_walk.out`; the earlier run on the observed range is
`cert_walk_observed.out`, worst d ≤ 8.36e-6 against ε_B = 9.52e-6).

`paddedPack2Net_all_cut_bounds` bounds non-row-aligned cuts and padding by γ ≤ 3n per block, about
0.0008μ, which is inside the 0.1μ reserve. Because n is arbitrary, no divisibility grain is needed.

The first review (2026-10-19) caught that the unpadded fringe form with n = ⌊π/(2f)⌋ would have put
dummies into Property F's rank count. That is fixed by this (f+1)-row padded form.

## Obligations, in order

1. ~~Hand proofs of the design-P invariants, including the frontier roles and a/c ≤ η.~~ Done:
   R1-PROOF.md §2.
2. ~~The aligned-cut/padding lemma.~~ Done: γ ≤ 3n via `paddedPack2Net_all_cut_bounds` (§4).
3. ~~Root separator, top window, final sorters, and the schedule at (4,5,3).~~ Done (§5–6).
4. ~~Interval-certify the walk-bound constants.~~ Done: `cert_walk.py` (the full-window
   run).
5. A complete paper proof, reviewed. R1-PROOF.md had one review; its fixes are applied, and a
   re-review is pending.
6. Lean. The 1419 package must be generalized to non-uniform blocks (UB-12's Stage 1b/2 estimate
   is 2.5–4k lines). It also needs the walk bound (negative association, Ville), the per-E fringe
   route, and the padded separator (`paddedPack2Net` exists in the tapered experiment).
