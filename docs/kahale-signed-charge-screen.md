# Signed quadratic witness charges at central ranks: the LB-08 screen

Exact 4 to 7 wire screen of the family parked from LB-30. Successor note to
[amortized witness charges](kahale-witness-charge.md). It does not improve 3.2706.

## Verdict

**Mixed: the narrow central family is dead and the wider one survives only as a finite fit, with no route to a rate.**

- **Dead. [proved, exact certificates]** With ranks restricted to the central band
  `{floor(n/2), ceil(n/2)}`, the quadratic family cannot certify `D(n)` at `n = 4, 5, 6, 7`. At `n = 6, 7`
  its exact optima are about `2.695` and `4.122`, and it needs more than `4` and `5`. A stronger statement holds at
  all four sizes: no function of the central witness state, of any degree, reaches the target (§3).
- **Alive at finite size. [proved, exhaustive]** With ranks `{2, ..., n-2}`, dropping only the extreme ranks,
  the family certifies `D(6) >= 5` and `D(7) >= 6`. The values are exactly `32/7` and about `5.04019`. These
  are known bounds. This is not a central family in any scale sense: it reads 3 of 5 and 4 of 6 ranks. The same
  window fails at `n = 4, 5`, where it is the central band.
- **Soundness.** At each `n <= 7` the inequality holds on every reachable image and every parallel layer, so it covers
  every network of that width, not one schedule. Nothing is known for general `n`. No all-`n` inequality was proved.
- **Scaling: no evidence for it, and one lift tested fails.** The margin over `D(n) - 1` falls from `0.571` at `n = 6`
  to `0.040` at `n = 7`. The conditional-baseline lift of the 6-wire charge reaches about 3.63 on 7 wires, against the needed 5
  (§6). No recurrence was found. `n = 8` is not refuted: ranks `3..5` have `V <= 39/7 = 5.571`, and 5 is needed (§5).

**The key fact.** At 7 wires the two central ranks reach only 4.12, and ranks `2..5` clear the target of 5 by 0.04.
The second is an LP fit with 2115 terms. No term structure, baseline rule or wire rule was found.

**No rate is claimed.** `liminf D(n)/lg n >= 3.2706` is unchanged.

## 1. The family

For a prefix image `R` (a set of 0-1 outputs), `F_(k,a,b)(R) = 1` iff some `x in R` has weight `k`, `x_a = 1`,
`x_b = 0`, `a < b`. For a set `C` of ranks, let `Q(n, C)` be all signed

```text
Phi(R) = sum w_pq F_p(R) F_q(R),   rank(p), rank(q) in C,   |rank(p) - rank(q)| <= 1,
```

including `p = q`. So the two witnesses may come from different inputs, which is the cross-image feature of LB-30.
`Phi(sorted) = 0` holds by construction, and there is no constant term. The requirement is

```text
Phi(R) - Phi(L(R)) <= 1   for every reachable image R and every nonempty parallel layer L.
```

`V(n, C)` is the maximum of `Phi(cube)`. Telescoping gives `D(n) >= V(n, C)`, so the family certifies `D(n)`
exactly when `V(n, C) > D(n) - 1`.

**Why this is not LB-31's family.** LB-31 read only zero baselines, hence global input weights at most 3, and has the
ceiling `3 ceil(lg n)`. Central ranks are not subject to that ceiling, and §3 gives the corresponding statement.

**Every network. [proved]** Layers use ascending comparators only, which loses nothing by the standard untangling
argument: any sorter becomes a standard-form sorter of the same depth. Images are closed under single comparators.
The catalogues are complete: 44, 581, 19334 and 1940593 images on `n = 4, 5, 6, 7`. With 231 layers, `n = 7` has
448,276,983 transitions.

## 2. Results

`S` is the number of distinct witness states, `q` the distance in the state quotient (§3), `D_C` the exact least depth
of a network sorting every input of weight in `C`. All entries are exact **[proved]**. Published values of
`D(n)` are **[published]**.

| `n` | `D(n)` | needs `V >` | ranks `C` | `S` | `q` | `D_C` | `V(n, C)` | certifies? |
|---:|---:|---:|---|---:|---:|---:|---|---|
| 4 | 3 | 2 | 2 | 19 | 2 | 2 | 2 | no |
| 4 | 3 | 2 | 1..3 | 44 | 3 | 3 | 3 | yes |
| 5 | 5 | 4 | 2, 3 | 261 | 4 | 5 | 4 | no |
| 5 | 5 | 4 | 1..4 | 567 | 5 | 5 | 1287/290 = 4.43793 | yes |
| 6 | 5 | 4 | 3 | 1151 | 3 | 3 | 2.69528 | no |
| 6 | 5 | 4 | 2..4 | 7442 | 5 | 5 | 32/7 = 4.57143 | yes |
| 6 | 5 | 4 | 1..5 | 17320 | 5 | 5 | 14/3 = 4.66667 | yes |
| 7 | 6 | 5 | 3, 4 | 78736 | 5 | 6 | 4.12170 | no |
| 7 | 6 | 5 | 2..5 | 623579 | 6 | 6 | 5.04019 | yes |
| 7 | 6 | 5 | 1..6 | 1453250 | 6 | 6 | >= 5.04019, not computed | yes |

The `n = 4, 5` values reproduce `docs/kahale-witness-charge.md` (3 and 1287/290). The full `n = 7` values are 258-digit
fractions and are stored in the certificate file.

The Farkas certificates are small at `n = 6`: 36 rows for each of `32/7` and `14/3` (half are reflections). At `n = 7`
they have 888 and 2038 rows. Each row is one comparator prefix and one layer. In the `32/7` certificate, 8 rows start at the
cube and 8 after one layer, and the rest start 6 to 11 comparators in. So the bound uses both ends of a network at once.

## 3. A ceiling for every function of the state

**Lemma. [proved]** Let `sigma` be any summary of an image. Form the graph on `sigma` values, with an edge `sigma(R) -> sigma(L(R))` for each real transition. If `f` is any function of `sigma` with unit layer drop, then `f(cube) - f(goal) <= q`, the distance from `sigma(cube)` to `sigma(goal)`. Telescope along a shortest path. Each step is a real layer on a real image, and
consecutive steps join at equal `sigma`, so a path may jump between networks.

This has no linearity assumption, so it covers quadratics, every higher degree, and tables. A path is a very short
certificate, stored with `kind: "path"`.

**Consequence. [proved]** `q <= D(n) - 1` for the central band at `n = 4, 5, 6, 7` (the table above). Any function of the
central witness state fails, at every degree and with any signs. So raising the degree does not rescue that family.
This is the one natural enlargement, and the path certificates answer it. I ran no other enlargement.

**Wider windows.** For the next window out, `q = D(n)` at `n = 4..7`: the pair state loses no depth
information there, and what limits `V` is the quadratic form, not the state.

**The rank-slice ceiling. [proved]** A function of the slices in `C` has range at most `D_C(n)`, the case
where `sigma` is the slice itself. At `n = 6`, `C = {3}`, a depth-3 network sorts every weight-3 input.

**Single rank, general `n`. [proved]** For `n = 2m`, `D_{m}(2m) <= D(m) + 1`. Sort each half, then compare `a` with
`2m-1-a` for all `a`. On weight `m` the halves are `0^(m-j) 1^j` and `0^j 1^(m-j)`, so the mirror pairs are complementary
and the layer sorts. So a charge on the rank `n/2` slice, of any form, gives at most `D(n/2) + 1`. Checked networks:

| `n` | `D(n)` | rank `n/2`, depth found | ranks `n/2 - 1 .. n/2 + 1`, depth found |
|---:|---:|---:|---:|
| 8 | 6 | 4 | 6 |
| 10 | 7 | 6 | 7 |
| 12 | 8 | 6 | 8 |
| 16 | 9 | 7 | not searched |

These are upper bounds from checked networks, half-cleaner or beam search.
The rate is unaffected: `D(n/2) + 1` has the same leading coefficient as `D(n)`. **This does not bound the rate of
single-rank charges.** It says that such a charge must already contain a sorting bound one level down.

For three ranks the half-cleaner gives nothing better than a sorter, and beam search found no network shallower than `D(n)`.
So the ceiling is a statement about one rank only.

## 4. The potentials

Rounded weights over `2^24` (and `2^30` for `n = 7`) are stored in the certificate file.

- `n = 6`, ranks `2..4`: 734 nonzero terms; ranks `1..5`: 866.
- `n = 7`, ranks `2..5`: 2115 nonzero terms, largest weight 1.87.

Exact integer checks on every transition:

| `n` | ranks | start | worst drop | start / drop | needs `>` |
|---:|---|---:|---:|---:|---:|
| 6 | 2..4 | 4.571428 | 1.000001 | 4.571424 | 4 |
| 6 | 1..5 | 4.666667 | 1.000001 | 4.666662 | 4 |
| 7 | 2..5 | 5.040195 | 1.000000007 | 5.040195 | 5 |

These are LP vertices, and the columns have many linear dependencies on real images, so individual weights have no
meaning. I looked for no sparse form and make no claim about the minimum term count. At these sizes the formula is not an
explanation.

## 5. Scaling: `n = 8, 10`

Exhaustive catalogues are out of reach here. A set of true rows gives an **upper** bound on `V`, so this tests whether the
family falls behind. It cannot show that the family keeps pace.

| `n` | ranks | `D(n)` | needs `V >` | upper bound on `V` | reading |
|---:|---|---:|---:|---:|---|
| 8 | 3..5 | 6 | 5 | 39/7 = 5.5714, exact dual, 74 rows | not refuted |
| 10 | 4..6 | 7 | 6 | none | stopped: value still 52076 at about 4250 rows |

**[proved]** for the `n = 8` bound, by the stored certificate. It came from 18627 sampled true rows. No lower bound on
`V(8, 3..5)` exists. At `n = 7` the same sampling reached only 5.73 after about 11000 rows against the true 5.04, so
sampled bounds run high and the true value at `n = 8` may be well below 39/7. **It does not show that the family keeps pace,
and it does not show that it falls behind.** The ticket's question at `n = 8, 10` stays open: `n = 8` needs an exhaustive
catalogue, which I estimate is far too large for this budget, and `n = 10` needs more compute.

## 6. Does the potential extend?

The ticket's route is a conditional charge at a baseline. The exact test is on 7 wires, with the 6-wire potential for ranks
`2..4`. Freeze one wire `t` to a value `v`, project to 6 wires and evaluate `Phi_6`. This is a true baseline charge,
with central rank shifted by `v`, and every fiber has `Phi_6(cube) = 32/7`.

| lift to 7 wires | start | worst drop | start / drop | needs `>` |
|---|---:|---:|---:|---:|
| single fiber, best of 14 (`t = 2`, `v = 0`) | 4.5714 | 3.23 | 1.42 | 5 |
| single fiber, worst of 14 (`t = 6`, `v = 0`) | 4.5714 | 5.00 | 0.92 | 5 |
| uniform mean of 14 fibers | 4.5714 | 1.48 | 3.09 | 5 |
| best signed combination of 14 fibers | 3.628 | 1.000 | 3.628 | 5 |

So the lift gains nothing in value, and unit drop fails on one fiber by a factor of 3 to 5. Averaging repairs part of that
only by giving up value. This is the replication check of `docs/kahale-witness-charge.md` §5 made exact on one size.
**[numeric, exhaustive at `n = 7`, floating point]** It tests one lift of one potential, not every recurrence.

**Values against depth.** Across all ranks, `V` is `3, 4.44, 4.67` at `n = 4, 5, 6`, against `D = 3, 5, 5`. Too few
points for any trend, and I do not fit one.

## 7. What a rate would need

**[conjecture]** All three, none of which exists:

1. A rule giving `w_pq` for every `n` from ranks and wire positions. No such rule was extracted.
2. A proof of unit drop on every reachable image for every `n`. §4 of the witness-charge note shows the inequality is false on
   arbitrary domains, so the proof has to use realizability. That is the open core of LB-24, LB-33 and LB-34 in another
   form: a statement about all networks, not about a schedule.
3. A value of at least `c lg n` with `c > 3.27`. The test above shows flat value under the natural lift.

Finite feasibility at `n = 6, 7` supplies none of these. It only says that an LP with thousands of free coefficients can
fit a table with known depth. The 7-wire margin of 0.04 shows how little room the fit has.

## Decision

- **Rejected:** the family `Q(n, C)` with `C` the central one or two ranks, and any function of that witness state.
- **Not rejected:** the family with ranks `{2, ..., n-2}` or all ranks, as a finite object. It is parked, not because it is
  promising, but because `n = 8` was not refuted. It has no scale-compatible form.
- **Do not reopen unless** someone has a rule for the weights (item 1 of §7). Refitting at larger `n` without one would produce
  more tables.

## Not verified

- `V(7, ranks 1..6)` was not computed; only `>= 5.04019`, by inclusion.
- `n = 8` and `n = 10` have no exhaustive check. The bound in §5 is a relaxation, and `n = 10` has no bound.
- The `n = 7` and `n = 8` LPs and the §6 lift ran from scratch drivers, not from the committed CLI. `cp_mosek` copies the 7-wire
  driver and was not rerun on 7 wires; the sampled `n = 8` Mosek loop and the §6 lift are not committed. The stored certificates
  carry the §2 and §5 claims. §6 is floating point and has no certificate.
- `D_C` beyond `n = 7`, and the three-rank depths in §3, are upper bounds. No lower bound was attempted.
- The `n = 7` potential check needs numpy. It is separate code from the screen, but it is not standard-library-only.
- Standard-form reduction is the classical argument, not re-derived in Lean. No Lean was added.
- No sparse potential was sought.

## Reproduce

```text
python -B lower-bound/experiments/scripts/kahale_signed_charge_check.py docs/kahale-signed-charge-certificates.json
```

The checker recomputes every image from stored comparator lists, uses no solver and imports nothing from the screen. It
checks: Farkas rows (exact fractions, every raw monomial), quotient paths, slice sorters, and potentials on all transitions.

To regenerate, about 25 minutes for `n <= 6`:

```text
python -B lower-bound/experiments/scripts/kahale_signed_charge_screen.py \
  --output docs/kahale-signed-charge-output.txt --certs docs/kahale-signed-charge-certificates.json \
  --wires 4 5 6 --selectors
```

`--wires 7 --lp-wires 7 --solver mosek` is the intended 7-wire run, about 1 hour per family and several GB; see "Not verified".
The sampled tools `WordImages` and `walk_pool` are in the script.
HiGHS and Mosek give only candidate weights and multipliers; exact Dixon lifting and integer checks make the claims.
Output: [text](kahale-signed-charge-output.txt), [certificates](kahale-signed-charge-certificates.json).
