# Comparison information on the Kahale-extremal schedules (LB-03)

Claim labels:

- **[proved]** a complete argument here (not kernel-checked; no Lean was added).
- **[hand]** a hand-level argument with a step left informal.
- **[numeric]** a finite computation or sampled estimate, with no asymptotic force.
- **[published]** a cited result.
- **[conjecture]** a reading of the data.

## Verdict

**Rejected. No coefficient above 3.2706 comes out of this ticket, and two of the three
stop conditions fire.** The third depends on the schedule and is not settled.

1. **Waste is not a free variable. [proved]** Every sorter of depth `d` has total waste
   exactly `M - lg n!`, a function of `(n, d)` alone. So "waste forces depth" is the
   depth bound rewritten, not a second constraint to couple with Kahale.
2. **The candidate is not sound for every network. [proved, numeric]** In its marginal
   form, a recursive doubling network has equal heights at every gate and exactly zero
   marginal waste for `lg n` layers (§3.2). `tr` confirms this numerically at
   full depth (§3.3).
3. **It hits LB-26's obstruction exactly. [proved]** With the true `h_g`, the candidate at
   coefficient `c` is the LB-26 charging lemma with threshold `2/c` in place of `1/2`
   (§4). What is missing is the same lemma. Stopped here, as instructed.
4. **Certificate efficiency does not determine waste. [numeric]** The key number: at
   `d = 64`, `n = 16530`, both schedules pass the heights and wire relaxations, yet
   `Σ H(S_g) / lg n!` is **0.913 on the barrier and 1.83 on `tr`**. The barrier is short of
   the information a sorter needs, and `tr` has an 83% surplus.

**A side result, one network only. [numeric]** The barrier at `d = 64` fails a sound
information test: `Σ H(S_g) < lg n!`, certified at about 98% family confidence (§2.3). This
is a true statement about that network and carries no bound on `D(n)`.

**Correction to the ticket's budget. [proved]** Information alone gives about `2 lg n`,
not `lg n`: `n/2` bits per layer against `lg n! ≈ n lg n`. This agrees with `SURVEY.md`.
The `lg n` figure is fan-in. Either way it is below 3.27, so the conclusion is unchanged.

**No rate is claimed.** `liminf D(n)/lg n >= 3.2706` is unchanged.

## 1. Definitions

The screen's definition and the ticket's differ, so both are kept. Take a uniform random
permutation and a fixed gate order. `S_g` is the swap bit of `g`, `Y_g` the whole rank vector
after `g`, and `S_<g` all earlier swap bits.

| Name | Quantity | Role |
|---|---|---|
| marginal | `H(S_g)` | the binary entropy of the outcome, this screen's `h_g` |
| learned | `H(S_g \| S_<g)` | decision-tree information |
| forgotten | `H(S_g \| Y_g) = H(Y_(g-1)) - H(Y_g)` | **the ticket's `h_g`**, from LB-26 |

**The chain. [proved]** For every network,

```text
sum forgotten = lg n! - H(Y_final)  <=  sum learned = H(S)  <=  sum marginal.
```

`(Y_t, S_<=t)` determines the input, and `Y_t` is a function of it, so
`H(S_<=t | Y_t) = lg n! - H(Y_t)`. Conditioning gives the rest. On a sorter the two lower sums
both equal `lg n!`.

Only the marginal, and two relaxations of "learned", can be estimated at `n = N_d`. They
condition on the bits of the 2 feeding gates (`ctx1`) and also on the 4 gates feeding those
(`ctx2`), which is 6 bits. Conditioning on less gives an upper bound on `H(S_g | S_<g)`, so
`Σ marginal >= Σ ctx1 >= Σ ctx2 >= H(S)` up to sampling error. The true `h_g` is out of reach at
this size, as the proof plan warns. Waste below is `M - Σ(...)`, with `M = D floor(n/2)` and
`D = d + 2`, so it includes idle slots.

**Exact check. [numeric]** All three sums were computed on every permutation for Batcher and
the barrier at `n = 6..9`, and for doubling at `n = 4, 8`. The chain and the identities hold on all
of them (`exit_exact=0`). Sorted-block forgetting matches `4^k/C(2k,k) - 1` through `k = 10`.

## 2. Question 1: the numbers

### 2.1 Totals

`T = 4096` permutations, Miller-Madow corrected, capped at 1 bit per gate. The forced column is
`1 - lg n!/M`, the waste of **any** sorter at that `(n, D)`. Both schedules pass heights and wire at
every row. `H_up` is the upper estimate of `H(Y_final)`, the sum of per-wire Lehmer-digit entropies.
Replicates with seed 2 at `d = 48, 64` agree within 0.05% on `Σ H`.

| d | n | D/lg n | forced | barrier waste/M | `tr` waste/M | barrier `ΣH/lg n!` | barrier ctx2 | `tr` `ΣH/lg n!` | `tr` ctx2 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 40 | 161 | 5.73 | 0.716 | 0.591 | 0.524 | 1.443 | 1.363 | 1.677 | 1.488 |
| 44 | 344 | 5.46 | 0.696 | 0.589 | 0.470 | 1.351 | 1.282 | 1.742 | 1.545 |
| 48 | 738 | 5.25 | 0.676 | 0.596 | 0.421 | 1.249 | 1.198 | 1.788 | 1.610 |
| 52 | 1593 | 5.08 | 0.659 | 0.605 | 0.386 | 1.159 | 1.109 | 1.802 | 1.622 |
| 56 | 3459 | 4.93 | 0.644 | 0.620 | 0.351 | 1.068 | 1.022 | 1.823 | 1.651 |
| 60 | 7545 | 4.81 | 0.631 | 0.636 | 0.323 | 0.986 | 0.947 | 1.833 | 1.675 |
| 64 | 16530 | 4.71 | 0.619 | 0.652 | 0.303 | **0.913** | 0.881 | **1.831** | 1.693 |

Two readings. **[numeric]**

- The barrier's visible waste rises, from 0.59 to 0.65, and passes the forced value between
  `d = 56` and `60`.
- `tr`'s falls, from 0.52 to 0.30. At `d = 64` it is under half the forced value and under the
  0.4286 that coefficient 3.5 would need. Marginal waste misses much of the true waste on `tr`.

**Does waste per depth stay away from zero?** It depends on which waste. **[proved]** The true waste
of a sorter does: by Kahale and §3.1 it is at least `0.3885 M` minus lower-order terms. **[numeric]** Marginal
waste shows no floor: it rises on the barrier and falls steadily on `tr`. No limit is extrapolated from either.

### 2.2 By stage, `d = 64`

Mean waste as a fraction of the `n/2` slots, by quarter of the depth, idle slots included.

| Quarter | barrier idle | barrier waste | `tr` idle | `tr` waste |
|---|---:|---:|---:|---:|
| 1 | 0.000 | 0.246 | 0.000 | 0.246 |
| 2 | 0.001 | 0.706 | 0.001 | 0.660 |
| 3 | 0.001 | 0.819 | 0.000 | 0.014 |
| 4 | 0.378 | 0.824 | 0.000 | 0.270 |

**[numeric]** The barrier and `tr` differ in the last half, which is exactly the part `tr` rewrites. Near-fair
gates (`H >= 0.9`) are 11% on the barrier and 48% on `tr`. All depths are in the output file.

**Stage waste is not canonical. [proved, numeric]** The stage profile depends on the accounting. Let
`L_t = H(S_<=t)` and `F_t = lg n! - H(Y_t)`. Then

```text
L_t - F_t = I(S_<=t ; Y_t)  >= 0,
```

which vanishes at `t = 0` and at the end of a sorter. It is an endpoint-zero bank that the accounting
itself creates. In the exact 8-wire Batcher network, the last layer has 3 gates and is worth 2.94 bits as forgotten, but 1.71
bits as learned. Only the total is invariant, and §3.1 shows the total is forced.

### 2.3 Against the information requirement

**A sound test for one network. [proved]** A sorter needs `Σ H(S_g) >= lg n!`. So
`H(Y_final) >= lg n! - Σ H(S_g)` for every network.

**[numeric]** The barrier point estimate falls below `lg n!` between `d = 56` and `60`, and `ctx2` falls below
it at the same place. To guard against small-`p` gates, the certify run takes `T = 65536` and a per-gate
Wilson interval at `z = 5.5` (two-sided about `3.8e-8` per gate, about 2% over all gates):

| d | `Σ H` plug-in | `Σ H` upper | `lg n!` | certified? |
|---:|---:|---:|---:|---|
| 56 | 38117 | 39634 | 35681 | no |
| 60 | 85123 | 88685 | 86312 | no, only the point estimate is below |
| 64 | 189693 | 198004 | 207792 | **yes**, `H(Y_final) >= 9788` |

## 3. Question 2: the charge

### 3.1 What is sound: waste costs depth

**[proved]** With `M = d floor(n/2)` and `G` gates, the LB-26 identity gives, for every sorter,

```text
(M - G) + sum_g (1 - h_g) = M - lg n!.
```

Since `H(S_g) >= h_g` in total, also `(M - G) + sum_g (1 - H(S_g)) <= M - lg n!`. So any lower bound `W` on
waste gives `d >= (lg n! + W)/floor(n/2)`. This half of the tradeoff is sound and trivial.

Its price is the catch. The left side is constant over all sorters at `(n, d)`. Height slack against `U_d` and
information slack against `lg n!` are also functions of `(n, d)` only. So a coupled inequality
"height slack + information slack >= X" between those totals is a depth statement with no
independent variable. Any real coupling has to work layer by layer, inside the network.

**The scale. [proved]** A fraction `ρ` of forced waste corresponds to coefficient `c = 2/(1 - ρ)`.

| Coefficient | Forced `ρ = 1 - 2/c` |
|---:|---:|
| 2 | 0 |
| 3.2706 | 0.3885 |
| 3.5 | 0.4286 |

The gap is `0.0401 M = 0.0201 n d` bits, that is, `0.02 d` bits per wire. So waste can matter at the 3.27
scale only as an excess of `0.02 nd` above what Kahale already forces. The 0.3885 is Kahale restated, not
new evidence.

**The ticket's test is vacuous at these sizes. [proved]** It asked whether `ρ` is well above 0.388. At `N_d`
the forced value is already 0.62 to 0.72 for **every** sorter, because `N_d` carries the polynomial loss and
`D/lg n` is 4.7 to 5.7. Only the excess over forced means anything.

### 3.2 The candidate, stated

Let `e_g` in `[0, 1]` measure certificate efficiency, with `e_g = 1` at a gate whose inputs have equal
zero heights and equal one heights. Let `W_t` be the waste of layer `t`, and `E_t = sum_(g in t) e_g`.

```text
(C-L)  W_t >= κ E_t + B_(t+1) - B_t      for every network and layer, κ > 0
(C-G)  W(N) >= (M - lg n!) + 0.02 n d - o(n d)
       for every network passing the certificate relaxations at (n, d)
```

| Form | Sound for every network? |
|---|---|
| C-L, marginal, no bank | **False. [proved]** Doubling, below. |
| C-L, marginal, bank of size `o(n lg n)` | **False. [proved]** Same network. |
| C-L, true `h_g`, no bank | **False. [proved]** Layer 1 of any network has `W_1 = 0` when full, and `e = 1`. |
| C-L, true `h_g`, bank with total range `o(n lg n)` but unbounded inside | **Open.** This is LB-26 (§4). |
| C-G, marginal | **False at tested sizes. [numeric]** §3.3. |
| C-G, true `h_g` | **Equivalent to the goal. [proved]** Since `W(N) = M - lg n! + H(Y_final)`, it says `H(Y_final) >= 0.02nd` on every relaxation-passing network, so no such sorter exists. It cannot be a step toward itself. |

**Doubling. [proved]** Let `R_t` on `2^t` wires compare `i` with `i + 2^k` at stage `k`, for `i` with bit `k`
clear. Before stage `k`, gates touch only wires agreeing on bits `>= k`. So `i` and `i + 2^k` lie in disjoint
isomorphic components with exchangeable inputs, hence `P(S_g = 1) = 1/2` exactly and `H(S_g) = 1`. By
the same isomorphism, the two heights agree on both sides. Thus `R_t` has no idle slot and zero marginal
waste, with `e_g = 1` at every gate of its `lg n` layers. The output confirms equal heights at `t = 3, 10, 14`,
and a sample agrees with `Σ H = M` to `10^-4` at `t = 14`.

Follow `R_t` with any sorter. The result is a sorter whose first `lg n` layers have no marginal waste, which is
`1/c` of its depth at coefficient `c`. So a marginal charge needs a bank holding about `κ (n/2) lg n` mid-run.

**Why efficiency does not push waste up. [hand]** Equal heights mean similar certificate sizes, which tends
to mean similar marginals, which tends to mean `p` near 1/2. The natural correlation between efficiency and
marginal information has the wrong sign for this candidate.

**True `h_g` at a gate. [numeric]** Heights do not control it. On 5 wires the signature `(2,3),(2,3)` has `h_g`
from 0.39 to 1, as recorded in `kahale-proof-plan.md`.

### 3.3 Waste is not a function of certificate efficiency

**[numeric]** `tr` and the barrier have the same `(n, D)` and both pass heights and wire at every tested `d`. That is
the hypothesis C-G would use. At `d = 64`:

| | barrier | `tr` | needed for C-G |
|---|---:|---:|---:|
| `Σ H - lg n!` | -18085 | +172694 | at most -21158 |
| `H(Y_final)` | 9788 to 125570 | at most 8054 | at least 21158 |
| wrong wires | 99.6% | 17.2% | |

Batcher, a true sorter, is the control. It fits at `n = N_d` for `d = 40, 44`, with `ΣH/lg n!` of 1.76 and 1.86 and only 70%
and 63% of the forced waste visible as marginal waste. So the marginal misses 30 to 37% of the waste on a network that really sorts.
At `d = 48` it needs depth 55, so that control row in the output is not at the same `(n, D)`.

### 3.4 The size of the excess

This is the third stop condition, and **it is not settled**. Excess over forced is `H(Y_final)`, and the threshold is
`0.02 nd`. **[numeric]**

| d | barrier `H_up/0.02nd` | `tr` `H_up/0.02nd` |
|---:|---:|---:|
| 48 | 3.57 | 0.012 |
| 52 | 4.28 | 0.036 |
| 56 | 4.89 | 0.105 |
| 60 | 5.45 | 0.216 |
| 64 | 5.93 | 0.381 |

On the barrier the excess may exceed the threshold: the certified lower bound at `d = 64` is 0.46 of it, the
point estimate 0.85, the `ctx2` estimate 1.17, the upper estimate 5.93. `tr` stays below it through `d = 64`, but **its ratio is
growing**, and on this trend it could cross a little past `d = 64`. So `tr` shows only that the barrier's excess is mostly a defect of the
barrier at these sizes. It does not show that the excess of the best schedule is below `0.02 nd`. **[conjecture]** `tr`'s trend is the
known defect of LB-34 and LB-35 and says nothing about schedules in general.

## 4. Question 3: LB-26's obstruction

**Yes, exactly. [proved]** LB-26's target with threshold `θ` is

```text
sum_g (h_g - θ)_+  <=  sum_g (θ - h_g)_+  +  θ (M - G)  +  o(n lg n).
```

The positive and negative parts combine, so this is `sum_g h_g - θ G <= θ (M - G) + o(n lg n)`, that is,
`lg n! <= θ M + o(n lg n)`. With `θ = 2/c` it is coefficient `c`. The plan's `θ = 1/2` is coefficient 4; coefficient 3.5 is `θ = 4/7`.

And C-L with true `h_g` sums to that same inequality, once `κ Σ E_t` is large enough to pay for `ρ M`. So the two routes
ask for one thing, and the coupling supplies only the extra hypothesis that certificates are efficient. It runs into each
piece of the known obstruction:

1. **Excess needs paying for. [proved]** High-information gates exist with `e_g = 1` (layer 1). They must be paid by
   a bank whose range inside the network is not controlled by its endpoints, and the proof plan's stop condition applies.
2. **Layers beat their gates. [numeric]** Sorted blocks of size `k = 10` have marginal 10 bits, learned 7.45 bits and
   forgotten 4.68 bits on a single layer. The marginal cannot see the dependence, and the true `h_g` is order-dependent inside a layer.
3. **The new hypothesis adds nothing usable. [numeric]** §3.3: efficient networks can sit on either side of `lg n!`, so a
   charge cannot read waste from efficiency. A stability statement would be needed, that near-extremal height populations force a
   near-unique schedule. But `tr` rewrites the last half of the depth and still passes.

**Why the extremal-schedule idea does not help. [hand]** SURVEY route 3 hoped to avoid the universal saving that route 7 needed by using
only extremal schedules. But any sorter at coefficient below 3.5 is near-extremal for Kahale, so the "restricted" statement covers
every network that matters. The restriction removes nothing.

## 5. Not verified

- Nothing here is kernel-checked. No Lean was added.
- The true `h_g` and `H(S)` were computed only at `n <= 9` (all permutations) and on sorted blocks through `k = 10`.
- `Σ marginal`, `ctx1`, `ctx2` at `n = N_d` are sampled. The Miller-Madow correction is a heuristic. Only the certify row at
  `d = 64` has a stated confidence, and it assumes the Wilson interval's coverage holds at `p` near 0.
- `H_up` is an estimate of an upper bound. Rare strays are undersampled, so on `tr` it may be low. The LB-34 strays are not sampled here.
- Heights and wire relaxations were rechecked. The pair relaxation was not rechecked on `tr` here (LB-35 reports it through `d = 56`).
- The 5-wire `h_g` range and the block closed form are taken from earlier notes; only the block form was recomputed.
- `0.02 d` is the asymptotic gap. At `N_d` the polynomial loss dominates, so §3.4 compares unlike scales and is not a rate.
- No bank was searched. C-L with a bank is left open, not refuted.

## 6. Reproduce

Run from the repository root. The full run took about 15 minutes of wall time on at most 4 cores. No job was killed.

```sh
S=lower-bound/experiments/scripts/kahale_information_screen.py
python $S exact 6 7 8 9
python $S blocks --kmax 10
python $S butterfly 3 10 14 --T 4096
python $S control 40 44 48 --T 4096
python $S screen 40 44 48 52 --T 4096
python $S screen 56 60 64 --T 4096
python $S screen 48 64 --T 4096 --seed 2
python $S certify 56 60 64
python $S table <screen output files>
```

Raw output with every `exit_*` status: [`kahale-information-screen-output.txt`](kahale-information-screen-output.txt).
