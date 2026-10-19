# UB-30: the tapered candidate re-priced with the walk bound

Ticket UB-30 · branch `ub-30-tapered-walk` · Claude (Opus 5.5) · 2026-10-19.

**Claim level.** This is a re-price of a *conditional* candidate. The tapered 945 price
([`../tapered/SUB1000-CANDIDATE.md`](../tapered/SUB1000-CANDIDATE.md)) depends on the open
scheduler and rank-profile gates of UB-22 and UB-24
([`../../backlog/tapered-recovery-plan.md`](../../backlog/tapered-recovery-plan.md),
[`../tapered/UB-24-RANK-PROFILE.md`](../tapered/UB-24-RANK-PROFILE.md)). This note changes only
the large ordinary separator, so every one of those gates stays open and nothing below is a
sorting theorem.

What is checked:
- The invariant budget and the provider fits are exact rationals.
- The bulk is the walk bound of [`../walk-bound/ROUND2.md`](../walk-bound/ROUND2.md): a reviewed
  hand proof with floating-point constants.
- The fringe is interval-certified with the F2ROUND route plus the tight R2 tail of
  [`../walk-bound/FRINGE-CERT.md`](../walk-bound/FRINGE-CERT.md).

The accepted coefficient remains 1419.

## Result: 945 → 792 (conditional)

The candidate's invariant constants are kept exactly:
- (k, A, ν) = (64, 64, 1/16), δ = 2^-25, ε_B = 2^-21, δ_F = 128/4095.
- The recovery plan's μ′ = (63/64)·17/71,565,312.
- ε_F = 511/2^32, so J = ⌈1/ε_F⌉ = 8,405,025.

Only the large ordinary provider's row height changes. It had to be 2^34 because the BULK2 bulk
bound reaches ε_B = 2^-21 only there. The walk bound reaches it at lg m = 31.12. The fringe binds
above that, at lg M ≈ 31.63 (smallest certified f ≈ 25,100). M = 0.875·2^32 is chosen with margin;
any M from there up to 2^32 − 1025 also fits.

| item | tapered (recovery plan, UB-22) | re-priced |
|---|---|---|
| row height M | 2^34 + 2^28 | 2^31 + 2^30 + 2^29 (lg 31.81) |
| bulk d at M | BULK2: ≤ 2^-21 at 2^34 | walk bound: 3.34e-7 vs 2^-21 = 4.77e-7 (1.43× margin) |
| fringe f | 131,040 | 28,200, in the window [28,114, 28,551] fixed by M |
| fringe certificate | package's 131040 witness | ln(2P1) ≤ −3441, ln(2P2) ≤ −2107 (budget −6.9) |
| half-port fit, normalized by C (with padding) | 8.75e-8 (8.74e-8) | 9.34e-8 (padding included) |
| cohort support, normalized by C (with padding) | 9.17e-10 (8.60e-10) | 4.51e-10 (padding included) |
| rows | < 2^35 | < 2^32 |
| node depth | 3·S(35) = 1890 | 3·S(32) = 1584 |
| exact small-bag cutoff | a ≤ 2^60 (S(60) = 1830) | a ≤ 2^55 (S(55) = 1540) |
| conditional coefficient (3 nodes per 6 bits) | 945 | **792** |

Here S(q) = q(q+1)/2 is the Batcher depth. Large bags (a > 2^55) have n ≥ 9.5×10^6 columns, and
the padded height m = ⌈a/n⌉ is at most M + 393.

The walk bound is n-uniform for n ≥ 16, with two caveats: p is sampled on a 1/64 grid, and the
continuous-p supremum and interval certification of its constants are still open. It is
evaluated at both M and M + 1024 (3.3446e-7 at each); monotonicity in m is observed, not proved.

Padding (m·n − a < n ≤ a/M dummy wires) is charged once against both provider margins. It is 4.6×
larger relative to C than at the old M and takes about 37% of the support margin. Aligned-cut
errors are not charged; they are open, as in the recovery plan, and must fit in the remaining
about 4.5e-10·C.

The fringe window is tight by construction. Two conditions, one from each side, fix f to a window
about 1.6% wide, proportional to M:
- **Lower end:** support, μ′·M/δ_F.
- **Upper end:** the half-port, (s − E_pos)·M/2 − 1.

So f is not a free parameter. The fringe must certify at about 7.5×10^-6 of the row height.

Reproduce with:
- `python -I tapered_walk_screen.py` → `tapered_walk_screen.out`. It first reproduces SUB1000's
  2.54003e-8 margin and the recovery plan's 1.6150e-8, 8.7487e-8 and 9.1697e-10. (With the
  200/2^34 wire allowance of `WireRoundingBudget.lean` the scalar margin is about 8.5e-9 with μ′,
  still positive and untouched by this re-price.)
- `python -I ../walk-bound/fringe_cert_search.py 28200 8405025` → `fringe_cert_f28200.out`. The
  exact route passes. The three closed-form (Lean-shortcut) checks fail, as at V0.
- `python -I ../walk-bound/fringe_cert_search.py min 8405025 20000 28200` →
  `fringe_cert_min_J8405025.out`, and `... min 9649000 20000 34000` → `fringe_cert_min_J9649000.out`.
  These give the smallest f on the search's parameter grid (g1/f ∈ {.2, .3, .4, .5}, c ∈ {2/5, 1/2}),
  not a lower bound for the proof route.

## What did not change

The 792 is conditional on the same gates as 945. The re-price leaves the scheduler gates as they
were, but it enlarges one provider gate:
- **UB-22.** The exact small-bag provider and the large ordinary provider contract. The re-price
  replaces the plan's M and f.
  - The exact cutoff falls from 2^60 to 2^55. Every bag with actual size in (2^55, 2^60], including
    top, bottom and frontier bags, now needs a scramble provider instead of the exact sorter.
  - The f window is only about 1.6% wide, so a frontier bag whose a/C differs from ordinary by more
    than about 1% needs its own fringe/port contract. This was already true above 2^60; the range is
    now larger.
- **Lean scaffolding for the old height.** The tapered large-provider scratch modules
  (`CandidateBulkExistence`, `CandidateBulkProvider`, `TruncatedFringeProvider` / `F2Params.std`) are
  tied to m ≥ 2^34, f = 131040 and J = 86e6. They would have to be redone at M ≈ 2^31.81, f = 28,200
  and J = 8,405,025, with the walk bound; negative association is not in Mathlib (ROUND2 §7).
- **The bootstrap/seed.** `BootstrapStageOneProvider` still uses 2^43 rows and the 131,040 fringe.
  That is a one-off cost, but SUB1000 notes that its additivity is itself unproved.
- **UB-24.** The ancestor-reserve laminar invariant and coordinated retirement balance. The
  current local rounding contract admits two splits that differ by two wires at a retiring
  block. The plan also needs the static-debt bootstrap profile, the six-stage signed rank
  recurrence, upper-retirement purity and terminal localization.
- **The final assembly.** Depth, padding and arbitrary n.

## Next gate: rows < 2^31 (744) needs a better fringe, not a better bulk

At M = 2^31 − 2^12, the bulk needs ε_B = 5.08e-7. The invariant budget can pay that by taking δ
down to 2.60e-8 (rounding charged at the 2^34 frontier), which gives J = 9.65×10^6. The fringe
window there ends at f = 16,314. The smallest f on the search grid is 25,125 at J = 8,405,025 and
27,000 at J = 9.649×10^6, so 744 needs a fringe floor about 1.65× lower.

The floor comes from the R1a tail slope, not from the probabilities. At the 792 point:
- λ_a = 28 is barely positive, while the failure exponents are below −2000.
- In λ_a = −(ts + c·β), the term ts = (J/(g1+1))·ln(e²(g1+1)²/D) is the union over
  top-of-column positions. That union is the fringe's analogue of the union over input states
  that the walk bound removed from the bulk.
- Balancing ts against the Chernoff gain gives f ∝ √(J·ln f).

A walk-style fringe argument that replaces this union is the concrete next step for 744. Unlike
the R2 tail of FRINGE-CERT.md, this is not a lossy tail estimate: the per-E exponent itself is
positive for large E.
