# Obligations 2–3 at the re-priced V0 point: certified fringe and exact Chvátal conditions

UB-29 · 2026-10-19 · Claude (Opus 5.5). **Claim level: interval-arithmetic certificate (fringe) and
exact rationals (Chvátal's conditions). It relies on one new rigorous bound, the R2 tail of §3,
which is a hand proof reviewed once (§6).** Nothing here is in Lean.

## Summary

The re-priced V0 point is the unmodified Chvátal design at new parameters, with stronger proofs:

| item | value | status |
|---|---|---|
| tree | `(k, A, nu) = (64, 2^11, 2^-5)`, `mu = (1 - 2^-10) 2^-28`, `delta = 1.38e-9` | (4.1)–(4.5) hold in exact rationals (`chvatal_conditions.py`) |
| separator | two rounds, `lg m = 38`; `eps_B = 2^-25` | bulk `d = 1.36e-8 <= 2^-25` (ROUND2.md, `n`-uniform) |
| fringe | `f = 32760 = 2^15 · 4095/4096`, `delta_F = 128/4095`, `J = 1/eps_F = 11 500 000` | **interval-certified**: `ln(2 P1) <= -3496`, `ln(2 P2) <= -1286` (`fringe_cert_v2.py`) |
| cost | `3 T(39) = 2340` layers per stage at `(x+y)/(xz) = 17/30` stages per bit | **1326** windowed |

So 1419 → 1326 needs no new mathematics beyond §3 (reviewed once) and ROUND2.md. What it still
needs: the package-side conditions listed in §5, and then Lean.

## 1. A model bug, found and fixed

`../lateral-repair/lateral_certfloor_model.py` computed `eps_F` from the largest `delta` that (4.2)
allows **at `eps_B = 0`**, and ignored the design's separator precision. That overstated `eps_F`.
At the V0 point the true `eps_F` is 8.9e-8 at `eps_B = 2^-25`; the earlier figure was 1.18e-7 at
`eps_B = 2^-24`. So the fringe target was too easy. The fix uses `eps_B = eps_sep`, which is
conservative when lateral repair is on.

Effect on the re-pricing (`reprice_b.out`, `reprice_na_b.out`; windowed values, ideal in
parentheses):

| design | before fix | after fix |
|---|---:|---:|
| V0, old proofs | 1418 (1286) | 1419 (1297) |
| V0, walk bound (proved round 2) | 1326 (1175) | **1326 (1197)** |
| S | 818 (708) | 818 (708) |
| L4′, `delta_F = 1/8` | 630 (519) | 630 (539) |
| L4′, `delta_F = 1/5` | 630 (503) | 632 (529) |

The windowed results barely change. The ideal values rise by up to 26, and the design points
move: V0 now sits at `eps_B = 2^-25`, `J ≈ 1.13e7`, where it was `2^-24`, `J ≈ 8.5e6`.

The UB-20 (lateral repair) table in `../lateral-repair/README.md` is superseded
(`cf_after_epsfix.out`). The fix evaluates the lateral rows conservatively, at `eps_sep` rather
than `rho · eps_sep`, so they now come out worse than no-lateral. Its parked verdict
(VERDICT.md, an overflow floor) does not rest on that table.

## 2. Certified fringe

`fringe_cert_v2.py` is `../lateral-repair/fringe_cert_param.py` plus §3. That file is a
parametrized copy of the accepted `best/notes/two-round/f2round/cert.py`; only `J` and `delta`
became parameters, as checked by diff. It uses exact-rational preconditions and `mpmath.iv`
outward rounding. At these points `E J / D >= 2 J / D > 10^4`, so F2ROUND's worst points are
admissible and the `n >= 16` clamp never activates.

| point | `f` | `g1 / g2` | `c, b` | `J` | `ln(2 P1)` | `ln(2 P2)` |
|---|---:|---|---|---:|---:|---:|
| V0 (window `lg m = 38`) | 32760 | 6552 / 29484 | 1/2, 5155 | 11 500 000 | −3496 | −1286 |
| V0 (`J` infeasible for (4.2)/(4.5), §4) | 32760 | 6552 / 29484 | 1/2, 5158 | 11 260 000 | −4450 | −1259 |
| V0, smallest on the search grid | ≈ 31364 | 6272 / 28227 | 1/2, 5503 | 11 500 000 | −4908 | −1033 |
| S (window `lg m = 33`) | 130048 | 52019 / 104038 | 2/5, 328 | 4 250 000 | −43 | −14628 |
| regression: package point | 131040 | 52416 / 104832 | 1/3, 17000 | 86 000 000 | −82466 | −9919 (closed forms −2076 / −227746 reproduced) |

The budget is `ln(1/1000) = -6.9` per side. The Lean-friendly closed forms (crude `lambda_b`,
regime-I/II slopes) **fail** at V0 and S. So would a Lean proof use the per-E route, as the
package's 92160 row already does, or new closed forms.

## 3. The new rigorous ingredient: a tighter R2 tail

**Why it was needed.** The original certificate bounds R2 at large `E` (regime II, `E > E2 = 2000`)
using `ln(e(B-1)s/(n T_s)) <= ln(ebE/(n Phi))`. Its slope is then `Lambda = q0 - c L_Y`, with
`q0 = ln(J Phi/(D e b))` and `L_Y = ln(e^2 J b/(D c^2))`. At the package's `J = 86e6` this is
positive. At `J ≈ 1.1e7` it is **negative**: `-2.76` at V0 (`J = 11.5e6`). The certificate then fails, although
the exact per-E bound, evaluated numerically, rises to about −15 500 near `E ≈ 16 000` and then
falls with slope about −0.65.

**The bound.** Take R2's per-E log bound at its worst point `n = (E-1)J/D` (F2ROUND §3–4):

```text
R2_E = lnY + ln n + max_{1<=s<=n} [ s ln(en/s) + T_s ln(e (B-1) s/(n T_s)) ],   T_s = Phi s + E.
```

1. `lnY <= ln(cE+2) + (cE+1) L_Y`, exactly as in the certificate. This uses `kappa = ceil(cE)`,
   the Y-count bound being increasing in `kappa` (precondition `(c+1/2)^2 <= bJ/(4D)`), and
   `n(B-1)/kappa^2 <= J b/(D c^2)`.
2. `(B-1)s/(n T_s) <= kappa1 s/T_s`, with `kappa1 = (E/(E-1)) bD/J <= ((E2+1)/E2) bD/J` for
   `E >= E2+1`. This uses `B - 1 <= bE` and `n = (E-1)J/D`.
3. Multiplying by `T_s > 0` gives `T_s ln(e (B-1) s/(n T_s)) <= T_s ln(e kappa1 s/T_s)`, with
   `T_s = Phi s + E` kept exactly. The original tail instead also replaced `s/T_s` by `1/Phi`
   inside the log.
4. Substitute `s = theta E/Phi` and use `n <= EJ/D` in `s ln(en/s)`. The bracket is then at most
   `E h(theta)`, where

   ```text
   h(theta) = (theta/Phi) ln(e J Phi/(D theta)) + (theta + 1) ln(e kappa1 theta/(Phi (theta+1))),
   ```

   and the maximum over integer `s` is at most `E H*`, with `H* = sup_{theta>0} h(theta)`.
5. `h` is concave: `h'' = -1/(Phi theta) - 1/(theta^2 (theta+1)) < 0`. `H*` is therefore
   certified like the certificate's `psi*`: bisect on `h'` in intervals, then
   `H* <= h(lo) + h'(lo)(hi - lo)`.
6. Hence `R2_E <= ln(cE+2) + L_Y + ln(J/D) + ln E - Lambda2 E`, with `Lambda2 = -(c L_Y + H*)`.
   The tail sum over `E > E2` is the certificate's `SumII` with `Lambda2` in place of `Lambda`.
   It keeps the `+1` in the exponent, which is conservative.

The certificate takes the smaller of the two valid tails and passes the slope check if either slope
is positive. At V0 (`J = 11.5e6`), `Lambda2 = 0.666`, with `H* = -11.30` at `theta ≈ 0.097`. That
agrees with the numerical slope of about −0.65. The range `E <= E2` is unchanged: the certificate's regime-I closed form,
checked per E.

The F2ROUND §4 monotonicity in `n` is not affected. The bound is evaluated at the same worst point,
and only the maximum over `s` is bounded more tightly.

## 4. Chvátal's conditions in exact rationals

`chvatal_conditions.py` transcribes (4.1)–(4.5) from DCS-TR-294, pp. 12–13, in the scaled form of
the Lean package (`cond42_scaled`, `cond45_scaled`, `cond44_real`, `paperRootEpsB_le_epsStar`).

* **Package point.** It reproduces the package. Every condition holds; (4.2) has LHS/RHS = 0.988
  and (4.5) has 0.966.
* **V0, `mu = (1 - 2^-10) 2^-28`.** This is the (4.3)/(4.4) cap, with the package's
  `1 - 2^-10` factor. With `eps_B = 2^-25` and `eps_F = 1/11.5e6`, `delta` is feasible in
  `[1.367e-9, 1.394e-9]`. At `delta = 1.38e-9`, (4.2) has 0.996 and (4.5) has 0.990.
* **The `J` the model gave is too tight.** At `J = 11.26e6` no `delta` on the search grid (step
  0.1%) is feasible; the window misses by about 0.1%. The `1 - 2^-10` factor in `mu` costs that much against the model, which uses the cap
  itself. `J = 11.5e6` restores the window, and the fringe still certifies at `J = 11.5e6` (§2).
* **(4.1), the root.** It needs `eps_* <= mu/k = 5.8e-11`. The package's root separator
  (`m = 2^79`, one round, Lemma 6.1) gives 1.3583e-11. The script checks (4.1) at the rational
  bound 1.36e-11, giving 0.234; that root value is a float figure.

## 5. Not checked here (package / Lean side)

* **Integrality and flow tables.** `FlowSizes7` and `levelSchedule7` (integral sizes, even `up`,
  the `t = 0, 1` special steps) and `mu c < 1` for every capacity are written for
  `(64, 2^12, 2^-6)` in Lean. The analogue here is `c <= 2^28`. Both need the Lean generalization.
* **Fringe geometry.** `f = 32760` assumes the package's relation between `f` and `m` scales as
  `f = m · f_over_m(k, A, nu)` at `m = 2^38`. That is the model's convention, matching
  131040 = 2^17 · 4095/4096 at the old point. The package's `ScrambleGeometry` should be checked
  for the new parameters.
* **The model's constraint `lg m >= 2(x+y)`.** Here `38 >= 34`. Chvátal's (5.1)
  `M >= 32 A^2 k^2` belongs to his own separator construction, which the package replaces.
* **Lean proof of the fringe.** It would need the per-E route or new closed forms (§2), plus §3.
* **Uniformity in `f`.** The certificate holds at the point `f = 32760` only. F2ROUND §5 leaves
  uniformity in `f` open, which matters if the geometry needs more than one `f`.
* **Bulk.** `d = 1.36e-8` at `lg m = 38` comes from `na_precision.py` (ROUND2.md, float constants)
  and is not interval-certified here.
* S and L4′ are structural variants (UB-12, tapered). Their own (4.2)-type conditions are not
  checked here; only S's fringe is certified (§2).

## 6. Review (2026-10-19)

An independent reviewer, working in a fresh context, checked §1–§5 and the scripts. It reran the
certificates and added its own float check of the exact per-E R2 bound against the §3 bound at
`E` = 2001, 3000, 10^4, 1.6·10^4, 10^5 and 10^6. The §3 bound is valid at every point. It is loose
near `E2` and tight asymptotically: −66 655 against −66 574 at `E = 10^5`.

**Confirmed.**
* §3, step by step: the worst point is the smallest `n` (the `ln n` coefficient is
  `kappa + 1 + s - T_s <= 0`), the `kappa1` direction, `n <= EJ/D` only enlarging the bound, `h'`
  and `h''`, the certified supremum, and the tail prefactor.
* `fringe_cert_v2.py` differs from its source only by §3.
* The search filter cannot accept a point where an exact-route check fails.
* `chvatal_conditions.py` matches the Lean scaled forms and reproduces the package. `mu` equals
  the (4.3) and (4.4) caps times `1 - 2^-10`.
* The model bug and its fix.

**Corrections (applied).**
1. The UB-20 consequence was misstated. The lateral table is now marked superseded (§1).
2. The certificate script exited 1 at the headline point, because the closed-form checks counted
   toward its verdict. It now reports the exact-route and closed-form verdicts separately, and
   exits 0 when the exact route passes.
3. Stale figures were updated: §3 now uses `J = 11.5e6`, S's `ln(2 P2)` comes from v2, and the
   smallest-grid row was re-searched at `J = 11.5e6`.
4. The (4.1) check was tautological. It now uses the root value 1.36e-11. "Infeasible at
   11.26e6" is labelled a grid result. The summary wording and the §5 list were corrected.
5. The script now checks `L_Y > 0`.
