# Screening cheaper separator stages at ideal separators (UB-09 follow-on 2)

Date: 2026-11-03. Claim level: **model** (optimistic floors), plus exact simulations
that are lower bounds for sampled scrambles. No new sorting bound; the best proved
coefficient is still 789.75.

## Verdict

No separator stage built from column sorts and random row scrambles reaches 300
under any analysis that is proved or derived. The best realistic figure is about
**333**: band repair plus merge-first under the centred tree analysis (R2c), at
attack-level separators and the measured attack tail. Only R3, the unreachable
zero-residual analysis, dips under 300, to 290.

The binding quantity is the **round-1 tail**, the mass of middle columns more than
W rows from the level. Under attack it decays only like 1/W (measured below). That
forces the band that replaces the third sort to be wide, which costs nearly a full
sort. With a tail 1000 times lighter, the same stage would give 244 at attack level
and 323 certified.

So the next lever is a round 1 whose tail is light *by construction*: a designed
(low-discrepancy) scramble, or a height-capped round 1. A cheaper sort will not do
it.

## Stages screened

All stages are priced by `scripts/stage_screen.py` on the tree model of
`TREE-PRICING.md`: (4.2)–(4.5), the attack ε_F table, and real parameters. S(q) is
q(q+1)/2.

| Stage | Depth | Leak |
|---|---|---|
| sort3 | 3S(L) | d(L), two rounds |
| sort2 | 2S(L) | E1(L), one round |
| band | 2S(L) + S(lg 2W) | d + 4T(W) |
| band+merge | S(L) − S(lg(f+1)) + S(L) + S(lg 2W) | as band; merge-first needs a redesigned wiring (UB-44) |
| band3 | 2S(L) + S(lg 2W₁) + S(lg 2W₂), with a third scramble | d/ρ + 4T(W₁); attack level only |
| floor2 / floor1 | two or one full sorts, zero leak | — |

Inputs:
- **T(W).** The round-1 tail of `sub500-screen/screen.py`; its certified form
  matches `cert_tail_W2e17` at 2^24.
- **Factor 4.** REVIEW-v7's correction to the band budget.
- **ρ.** The third-round leak gain, simulated (`scripts/three_round_sim.py`): 2.4,
  2.75 and 3.4 at m = 2^11, 2^13 and 2^15, about m^(1/8). The round-2 spread is
  only 18 to 39 rows, so the second band is narrow.

## Results: minimum slope, δ_F at its better value of 0.5 or 0.75

| Stage | Certified, R1 | Certified, R2c | Attack, R1 | Attack, R2c | Attack, R3 |
|---|---:|---:|---:|---:|---:|
| floor1 (one sort, no leak) | | | 128 | 109 | 91 |
| floor2 (two sorts, no leak) | | | 255 | 218 | 183 |
| sort2 | 578 | 596 | 552 | 569 | 522 |
| sort3 | 515 | 513 | 413 | 384 | 332 |
| band | 496 | 491 | 389 | 371 | 328 |
| band+merge | 456 | 454 | 364 | 348 | 304 |
| band3 | | | 408 | 374 | 333 |

The attack rows use an attack tail of 0.5 × certified.

With the measured attack tail of about 0.2 × certified:

| Stage | Attack, R1 | Attack, R2c | Attack, R3 |
|---|---:|---:|---:|
| band | 374 | 355 | 314 |
| band+merge | 350 | **333** | 290 |

Tail sensitivity, with the tail scaled by a factor (best δ_F):

| Tail factor | band+merge certified R2c | band+merge attack R1 | band+merge attack R2c |
|---|---:|---:|---:|
| 1 (as above) | 454 | 364 | 348 |
| 0.1 | 401 | 311 | 314 |
| 0.001 | 323 | 264 | 244 |

What the tables show:
- **One round is out.** The weak one-round leak forces m up to about 2^17–2^20,
  which costs more than the third sort saves.
- **A third round with narrow bands doesn't pay.** It lowers d, but d isn't
  binding; the round-1 tail term is.
- **Two full sorts already cost 218–255** at these trees, with zero leak. A stage
  with two full m-row sorts has only about 50–80 levels of room left for
  everything else.

## The round-1 tail is real (attack)

`scripts/round1_tail_attack.py`, at n = 1000 and m = 8192. The attack prices cells
landing in a middle set of fraction p at +1 and the rest at a negative value, then
lets every input column climb its walk. Each run is an exact run, so it is a lower
bound.

| W rows | Attack tail | Certified tail_frac | Ratio |
|---:|---:|---:|---:|
| 64 | 1.96e-3 | 1.22e-2 | 0.16 |
| 128 | 1.15e-3 | 8.64e-3 | 0.13 |
| 256 | 6.03e-4 | 4.25e-3 | 0.14 |
| 512 | 2.95e-4 | 1.50e-3 | 0.20 |
| 1024 | 1.28e-4 | 5.51e-4 | 0.23 |

The attack tail halves each time W doubles, so the 1/W law is a property of random
row scrambles, not slack in the certificate. The remedy has to change round 1
itself.

## Limits

- **Optimism.** Everything that tree_pricing assumes, plus:
  - band3's round-2 band escapes are free;
  - merge-first's run length is taken as f + 1;
  - the integer band width is free.
- **Attack-level inputs.** The attack d and E1 are scaled from single m = 8192
  measurements. The tail attack is one scramble at n = 1000.
- **Batcher sorts throughout.** No other small sorter changes S(q) by more than a
  few per cent at q ≤ 20.
- **No fringe charge for band repair.** The band's own F-cut leak (sub500's
  Σ(z − 2W)₊ blocker) is not charged, and it would make band worse.

Reproduce (BULK_CACHE = a scratch directory):
- `python scripts/stage_screen.py` (about 20 minutes);
- `python scripts/stage_screen.py band3`;
- `TAILSCALE=0.4 python scripts/stage_screen.py band,band+merge`;
- from the sub300 `prefix-flux` folder: `python <scripts>/three_round_sim.py 1000 8192`
  and `python <scripts>/round1_tail_attack.py 1000 8192 <scripts>`.
