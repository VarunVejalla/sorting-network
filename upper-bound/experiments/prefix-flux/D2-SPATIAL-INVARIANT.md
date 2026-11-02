# D2 spatial invariant: exact statement and first gate

Status (2026-11-01, corrected after independent review): the gate **fails** for
the tile-scatter construction, meaning the formal per-sender tile network applied
at every sender. No spatial invariant can hold for it on arbitrary inputs. Section
4 states the invariant for a sender-wide stage, which is the form that can still
hold. That form is a specification only: its provider is not proved. Section 7
reports the first test of it.

Evidence labels: **hand** (short argument given here, not kernel-checked),
**model** (exact finite computation), **crude** (order-of-magnitude budget).

## 1. Setting

Let `n = 8192 * 8^d` and `T = 262144`. The wires are addresses `0..n-1`. For
stage `t` and tree node `v`, `S_t(v)` is the sender set, and `native(v)` is its
address interval. `D2-DYNAMIC-SENDER-SETS.md` defines the routing: sets are
actual wire indices, with no wire permutation, and output slots are ordered by
increasing address.

The only stage network defined in Lean is `reflectedSenderFullTileStageNet` in
`D2ClippedCellRankInterval.lean`. It is a one-sender definition: it runs the core
independently on consecutive `T`-wire rank tiles, with comparators only inside a
tile. No whole-run network exists in Lean. No source defines comparators at the
root: every active root is `topDesc`, which has only a partition theorem, and root
initialization has been listed as open since `PLAN.md`. So "tile-scatter" here is
this note's construction, reading the per-sender definition at every sender,
including the root.

Sender-wide designs are recorded in the notes and are **not** covered by section 2,
since their columns cross all cuts: `RAGGED-13BIT-PROVIDER.md`,
`RAGGED-ALL-SENDERS-GATE.md` and `MODERATE-TAIL.md`, with about `a/8192` columns.
They are unproved, and their physical embeddings are open.

## 2. No-go: the tile-scatter network cannot sort

**Theorem (hand, with one model premise).** Assume every stage comparator lies
inside one tile of one active sender, as in the definition above. Assume also
that `S_t(v)` lies in `native(v)`. If `m = n/2` is never straddled by a root
tile, the false count of the address prefix `[0,m)` never changes during the
stages.

*Proof.* A comparator changes that count only if it joins a wire below `m` to a
wire at or above `m`. A non-root sender lies on one side of `m` by containment.
Root tiles are consecutive in address order, so a root tile joins the two sides
only if it straddles `m`. QED.

The model supplies both premises:

- `python d2_cut_crossing_gate.py` computes the straddling bound from exact
  bags. For `(3,3,2)` at depths 7, 8, 10, 20, 40 and 100 it is **0 of 2^(log2 n
  - 1)** keys. Containment passes for all active states, 217,470 of them at
  depth 100. The same run with `--params 3 2 2 --sparse-bottom` also gives 0.
- The zero is not needed: a shifted tiling allows at most one straddling root tile
  per stage, so at most `T/2` keys per stage against the `n/2` needed.
- Cumulative root mass after stage 0 is only `n/240` for `(3,3,2)` and `n/120` for
  `(3,2,2)`. So even a bag-wide network at the root after stage 0 crosses at most
  `n/480` keys. **Stage 0 alone must be a near-perfect halver on `n` wires.**
- `wire_partition_check.py --compressed` confirms routed sets equal static bags
  (rerun at depth 20; 32,750 routing cases). Earlier runs reached depth 120.

**Consequence.** Take the input with all false keys on the upper half of the
addresses. It needs `n/2` keys to cross `m`, and none do, so the staged network
does not sort it. The review confirmed this with an explicit wire simulation at
`n = 2^21` on an analogous schedule: the prefix false count stayed 0, and exact
bag-wide sorting did sort. Independent routing at depths 7 to 9 also confirmed
containment.

The midpoint alone does not make cleanup a full sorter: merge sort shows that
sorted halves plus a merger sort. It only forces work after the two halves are
handled. Using all cuts makes that much stronger, but "cleanup must be a full
sorter" is not proved. A bag-wide fix at the root alone escapes the midpoint, and
the same argument then applies at `n/16` unless the root itself sorts.

For a general cut the same argument applies through the cut's ancestors: at most
one straddling tile per ancestor per stage. That is `O(log^2 n)` keys in total,
so the network can only repair inputs whose cut defects are already that small.

The premises are checked at finite depths, not all depths; all-depth containment
is unproved. The conclusion is about this construction, not about D2 schedules or
sender-wide stages.

### Why earlier gates did not show this

- `D2GeometricProfileBudget.lean` is abstract and is never instantiated. Its
  `hdouble` cannot start at root stage 0, since tiles fall from `n/T` to `n/8T`.
  With global-threshold ideals, senders in the low half are wrong by `T` per tile
  at every stage, so a start away from `n/2` fails too (the l1 discrepancy is `n`,
  and `n/2` is one-sided). `idealTileMass` is free, so a sender-local ideal gives a
  valid start, but it then proves only local rank. The theorems are sound; the
  hypothesis needed for a global statement is never supplied.
- `D2-MARGIN-TAIL-TRANSFER.md` composes displacement per stage, but displacement
  starts near `n` on arbitrary input.
- The arbitrary-root LP assumed local tail caps at the root and still found large
  terminal error. That was the symptom of this gap, recorded then as a weakness of
  the relaxation.

### A fixed tile cannot be worth its depth

A bitonic sorter on `2^18` wires has depth `18*19/2 = 171` and sorts exactly. The
core has depth 276 and leaves an 832-wire band on the same `2^18` wires. So as a
tile-local network, the core is dominated. It only has a purpose if its columns
belong to a sender-wide matrix, and the checked theorems do not cover that case.

## 3. Price correction

Lean has `tfD2 d = 3*d - 14` for `(3,3,2)`, with `log2 n = 3*d + 13`, so the rate
is `(x+y)/(x*z) = 1`. The price of the formalized schedule is therefore
`276 * 1 = 276`, not 230, which leaves 24 units and not 70. The rate `5/6` belongs
to `(3,2,2)`: `tf(100) = 241` against 286. All the all-stage Lean work targets
`(3,3,2)`. Only `t=0` and `t=tf-1` lack an ordinary sender, so this is the limit;
finite values are lower (250 at `d=100`).

## 4. The invariant, for a bag-wide stage

Assume the input is a permutation, with `key_t(w)` the rank at wire `w`. For a set
of wires `P`, define the **bag rank defect**

```text
D_t(P,q) = #{w in P : key_t(w) < q} - #{w in P : w < q}.
```

This compares a bag's key ranks with its own addresses, so it needs no assumption
that keys start near their final positions. That is the essential change from
wire-level displacement.

### Exact facts (hand)

1. **Startup.** `S_0(root)` is all wires, so `D_0(root,q) = 0` for every input and
   `q`. All other bags are empty. No sortedness hypothesis is used.
2. **Conservation.** `sum_v D_t(S_t(v),q) = 0`, since the bags partition the wires.
3. **Receiver additivity.** `D_(t+1)(S_(t+1)(u),q)` is the sum of `D(P,q)` over the
   pieces `P` routed to `u`, evaluated after the senders run. Retained bags count
   as one piece.
4. **Exact-sort shape.** If a sender is sorted exactly, let `f` and `g` be the
   numbers of its keys and wires below `q`. For any slot interval `P`,
   `D(P,q) = |P cap [0,f)| - |P cap [0,g)|`. So the error sits only in slots
   between `g` and `f`, it has one sign, and `sum_P |D(P,q)| = |f-g|`.
5. **Terminal.** If every `D_tf(S(v),q)` is 0 and the terminal bags are address
   intervals, each bag holds exactly the keys of its range.

### Provider contract (open, the decisive unknown)

`Sep(tau)`: for every sender `S` of any size, Boolean input, and `f` false keys,
and every `s >= 0`, the stage output has at most `tau(s,|S|)` false keys in slots
`>= f+s`, and at most `tau(s,|S|)` true keys in slots `< f-s`.

`tau` must scale with `|S|`, since no constant-depth network gives an absolute
band on a large bag. The provider must be sender-wide. By section 2, a provider
built from disjoint address-consecutive pieces of size bounded well below `n`
fails, whatever the local quality (polylog times below `n` suffices for the
counting). A piece equal to the whole sender is the bag-wide case and is not
excluded. Scattered pieces fail a single-stage `Sep`, since a piecewise-constant
input is a fixed point; multi-stage scattered designs are not excluded.

### Invariant

For a node `v` at level `l` with `native(v) = [a,b)`, define for `rho >= 0`:

```text
X_t(v,rho) = #{w in S_t(v) : key_t(w) < a-rho or key_t(w) >= b+rho}.
```

`SRP(Xi, Lambda)` is the conjunction, for all inputs, `t`, `v`, `rho`, and `q`:

- `X_t(v,rho) <= Xi(l,t,rho)` (exterior strangers);
- `|D_t(S_t(v),q)| <= Lambda(l,t)` for `q` in `[a,b]` (interior alignment).

Together these bound `D_t` at every `q`, because for `q` outside `[a,b]` the defect
counts exterior strangers. Distance is measured in **addresses**, not tree edges:
a node can sit next to `q` in address while being far from `q` in the tree, and
fact 4 spills error to address neighbors.

### Obligations

- **Startup.** The state at `t=0` is immediate from fact 1, but the first step is
  not cheap: after stage 0 root mass is `n/240` in total, so the root sender's first
  output must already meet the bulk gate on `n` wires.
- **O1, sender to port.** From `Sep(tau)` and fact 4, bound `X` and `D` of each port.
  Slots do not determine addresses: a slot offset can jump a whole child hole, so
  this must use the static bag geometry (`g` is flat across a hole).
- **O2, up-capture.** Exterior strangers leave through the parent ends: the bag's
  left and right exterior mass plus `Lambda` must fit in the two end ports, or the
  excess must be charged to `tau`.
- **O3, receiver.** Sum over incoming pieces by fact 3. Only pieces within `Lambda`
  slots of `q` contribute to the interior term, which is what avoids a factor 9
  per stage.
- **O4, envelope closure.** `Xi` and `Lambda` must satisfy the resulting recurrence
  for every stage and role, including startup and ragged bags.
- **T1, terminal position.** The terminal bags must be address intervals. Sizes do
  not give this. The dynamic-set route therefore still owes the identity
  `S_tf(v) = native(v)`, or an equivalent. Model evidence exists; no Lean theorem
  does.
- **T2, cleanup.** If `Xi(l_term,tf,rho*) < 1` with `rho*` subpolynomial, every key
  is within `W = rho* + R_term` of its address, and the block-and-seam lemma in
  `D2-MARGIN-TAIL-TRANSFER.md` finishes at `o(log n)` depth when `W` is small
  enough. All-sized accounting and padding then follow as in `D2PowerPadding.lean`.

### Budget gate (crude)

Capacity is `cap(i,t) = N * A^i * nu^t / (A*nu*k)` with `A = 8`, `nu = 1/4`, so a
child at time `t` is 32 times `cap(i,t+1)` and a parent is 1/2 of it. Let `a_r` be
the stranger mass, as a fraction of capacity, at distance `r`. Assume up-ports pass
all strangers, and let `E(a)` be the mass escaping capture when a bag holds mass
`a`. Then

```text
a_r >= 256*a_(r+1) + E(a_(r-1))/2,   a_1 >= B/2 + 256*a_2,
```

where `B` is the bulk wrong-side leak. Since `a_(r+1) <= a_r/256`, and `E(a)/a`
increases with `a` in every table below, this closes iff

```text
E(a)/a <= 1/128 at a = B/2.
```

Splitting strangers by side might relax this to `1/64`. An earlier version of this
note asked for `eps <= 1/512` at mass equal to the fringe. That came from forcing
geometric envelopes and was stricter than necessary.

## 5. What survives

| Work | Status after this gate |
|---|---|
| Abstract flow, reserves, port grid, dynamic sets, routing | Valid schedule facts, independent of the provider. |
| Fit and static-bag work | Needed for O1 and T1, not made redundant by dynamic sets. |
| Fixed core, 448 transfer, tile aggregation | Sound, but only relevant to near-sorted inputs. Not a route to the startup hypothesis. |
| Block-and-seam cleanup | Valid and reusable for T2. |
| Coefficient 230 | Withdrawn for `(3,3,2)`; see section 3. |

## 6. Next gate

Do not add Lean bridges to the tile-scatter stage. Section 7 tests the provider.

## 7. Row-scramble tail test at height 4096

**Claim tested.** A sender-wide stage of three sorts and two random row-scramble
rounds at height 4096 (depth `3*78 = 234`; a fourth sort costs 312) meets the budget
gate using existing tail bounds.

**Verdict: rejected at height 4096.** This rejects the existing bounds at this
height. It is not an impossibility for random scrambles at all heights.

| Quantity at `m = 4096`, `n = 8000` | Value | Evidence |
|---|---|---|
| Certified bulk leak `B` | 0.00363 (14.9 rows) | walk bound, `na_precision.py` |
| Mean-field bulk leak | 0.00041 (1.7 rows) | floor |
| Gate mass `B/2` | 7.43 rows | fringe is 6 to 8 rows |
| Floor `E/a` at gate mass, `f = 6, 7, 8` | 0.20, 0.096, 0.032 | model; need 0.0078 |
| Certified one-round `E/a` | 0.55, 0.50, 0.45 | `moderate_tail.py` |
| Certified two-round F2 | no witness at `J >= 2`, or at `i >= 1/256` | grid search |
| Any-scramble floor on F2 `J` | 84, 120, 165 | hand, pyramid input |

Three separate reasons:

1. **Bulk forces too much mass.** At the certified `B`, even the mean-field floor
   misses by 12 times at `f = 7` (6 times against `1/64`). That floor is the typical
   behaviour of a random scramble, so no tail bound for random scrambles passes from
   this `B`. Tightening `B` by 1.35 times (`f = 7`; 1.14 to 1.65 across `f = 8` to
   `6`) would clear the floor. Mean field suggests a factor of 8.8 is available.
2. **Certified capture is far off.** Even at low mass the one-round bound gives
   `E/a` near 0.4, about 50 times above the need. It carries an entropy cost per
   column that does not vanish with small mass. F2 was built for sparse keys, and in
   the grid it certified only `f = 8`, `J = 1`, at about `1/1024` rows.
3. **An adversarial floor applies.** F2 is quantified over all inputs. Forcing
   height `h` after `k` rounds takes `c_k(h)` keys, with `c_0(h) = h` and `c_k(h) =
   sum_(r<=h) c_(k-1)(r)`, so `(f+1)(f+2)(f+3)/6` keys force an escape under every
   scramble pair. Thus `J <= 120` at `f = 7`: F2 at `J = 128` is impossible there
   for any scramble, though `1/64` is not excluded. Mean field does not see this,
   because it describes typical inputs. Whether these pyramids pack up to the gate
   mass was not checked.

**Limits.** The closure inequality is crude. F2 misses are limited to the searched
grid, and a certificate assertion counted as a miss. The floor is exact only as
`n` grows, and only for random scrambles, not structured ones.

**Height 8192 survives on floors only.** It costs `3*91 = 273`, leaving 27 units
for all other per-stage work and cleanup. Certified `B = 0.00216`, so gate mass is
8.85 rows against a 13 to 15 row fringe. The floor is `1.4e-5` at `f = 13`, and the
pyramid floor is `J <= 560`. Certified one-round capture is 0.33 at `f = 13`, about
40 times too large. Height `2^14` costs 315 and does not fit.

**Next gate.** A certified all-input capture bound at height 8192 with
`E/a <= 1/128` at about 9 rows of mass and fringe 13, using both scramble rounds. If
that cannot be reached, the three-sort `(3,3,2)` route is out of budget.

Reproduce with `python d2_sender_tail_gate.py --budget-gate` and
`python d2_f2_fringe_scan.py --fringes 7 8 --masses 1/1024 1/256 1/64 1/16 1/4 1
--inverse-eps 128 32 8 2 1`.
