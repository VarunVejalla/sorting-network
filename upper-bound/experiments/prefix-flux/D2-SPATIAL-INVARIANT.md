# D2 spatial invariant: exact statement and first gate

Status (2026-11-01, corrected after independent review): the gate **fails** for
the tile-scatter construction, meaning the formal per-sender tile network applied
at every sender. No spatial invariant can hold for it on arbitrary inputs. Section
4 states the invariant for a sender-wide stage, which is the form that can still
hold. That form is a specification only: its provider is not proved. Section 7
reports the first test of it. Section 9 gives the exact closure and the current
verdict on the three-sort `(3,3,2)` stage at height 8192. Section 10 costs a larger
fringe and finds no schedule geometry under 300 that closes. Section 11 bounds the
true worst-case bulk leak and parks the route. Section 12 gives an exact continuous-parameter no-go for the standard all-real-space quadratic-majorant method, but it does not rule out cube-constrained SOS bounds, other non-union arguments, or prove that the sender-wide stage fails.

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

### Budget gate (crude, superseded by section 9)

This gate is wrong in two ways, kept here because sections 7 and 8 quote it. It
charges strangers to all 8 children, though escapes on one side enter only the end
child on that side, so its gain 128 should be 16. Its "iff" is also false: it omits
feedback, so `E/a <= 1/128` at `B/2` was neither necessary nor sufficient.

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
8.85 rows against a 13 to 15 row fringe. The mean-field floor is `1.4e-5` at
`f = 13`, and the pyramid floor is `J <= 560`. Section 8 shows that this mean-field
floor is far too optimistic. Certified one-round capture is 0.33 at `f = 13`, about
40 times too large. Height `2^14` costs 315 and does not fit.

**Next gate.** Section 8 tests the certified capture bound at height 8192.

Reproduce with `python d2_sender_tail_gate.py --budget-gate` and
`python d2_f2_fringe_scan.py --fringes 7 8 --masses 1/1024 1/256 1/64 1/16 1/4 1
--inverse-eps 128 32 8 2 1`.

## 8. Capture gate at height 8192

**Gate tested.** `E/a <= 1/128` at 8.85 rows of mass and fringe 13, for every input,
under two random scramble rounds.

**Verdict: unreachable as stated for sampled random scrambles.** It cannot be
certified, because it is false for them. This is a measured attack, not a theorem
about all scrambles.

Adding one input key changes exactly one cell chain through the two rounds, which
makes a direct search cheap. `d2_capture_attack.py` builds inputs greedily, backward
from target columns, then frees idle keys and rebuilds. Mean field missed this
because it describes typical inputs, not chosen ones.

| Mass `i` (rows) | Attack `E/a`, `f=13` | Union vacuous to, `f=13` | Attack `E/a`, `f=15` |
|---:|---:|---:|---:|
| 1 | 0.0040 | 0.0038 | 0.0020 |
| 2 | 0.0056 | 0.0049 | 0.0040 |
| 3 | 0.0067 | 0.0063 | 0.0043 |
| 4 | 0.0078 | 0.0081 | 0.0053 |
| 5 | 0.0090 | not computed | 0.0058 |
| 6 | 0.0108 | 0.0138 | 0.0072 |
| 8.85 | **0.0208** | 0.0354 | 0.0115 |

Required: 0.0078, or 0.0156 if splitting strangers by side is valid.

**Evidence.**
- At `n = 4000`, `i = 8.85`, `f = 13`, one run gave 735 escapes against a limit of
  277. It was re-run as a full Boolean matrix with real sorts and row shuffles from a
  shuffled input, and gave the same count (`E/a = 0.0208`).
- Attack values come from `n = 1000` with three seeds. At `n = 4000`, masses 2 and 4
  match (0.0056, 0.0078). So the effect does not fade with column count, and larger
  senders are not protected.
- The attack gives a lower bound on the worst case, for sampled scrambles only.
- "Union vacuous to" is a first-moment estimate that treats target columns as
  independent. Below that `E/a`, the expected number of bad inputs exceeds 1, so a
  union bound over inputs proves nothing however it is tuned. Attack and estimate
  agree closely at masses 1 to 4, so both are probably near the true worst case.

**What this means for the route.**
- At the certified `B`, the gate fails by 2.7 times at `1/128`, and by 1.3 times at
  `1/64`. Fringe 15 still fails `1/128` by 1.5 times and passes `1/64`, but the worst
  sender sets the fringe, which is 13.
- `1/128` holds only up to about 4 rows of mass, so `B` must fall from 0.00216 to
  about 0.00098, which is 2.2 times tighter. Mean field (0.000245) leaves room, but
  no certified bound is near it. At `1/64` the crossing is near 7.4 rows, which needs
  about 1.2 times tighter, on a relaxation not yet justified.
- Even then, a capture proof must land within a factor of about 1.2 to 1.6 of the
  first-moment limit at masses 2 to 3, starting from a one-round bound near 0.33.
  The window is real but narrow.

**Limits.** The `1/128` closure is crude and could move in either direction. Atypical
or structured scramble pairs are not excluded: the only all-scramble floor is the
pyramid, `E/a >= 1/560` at sparse mass. This does not show that sub-300 is impossible.

**Next decision.** Section 9 replaces the `1/128` threshold used above. The attack
values stand. The factors 2.7, 2.2 and 1.3 above do not; section 9 gives the exact
ones. The rule set here was: if the exact closure still needs `E/a` below about 0.02
at the certified `B`, retire the three-sort `(3,3,2)` route at height 8192 and
reconsider the fringe size of the schedule.

Reproduce with `python d2_capture_attack.py` and `python d2_capture_limits.py`.

## 9. Exact closure

**Verdict: the three-sort `(3,3,2)` stage at height 8192 is retired on current
bounds.** At the certified `B` the exact closure fails even at attack-level capture,
so the rule in section 8 applies. This is a verdict on the contract route with sampled
random scrambles. It is not a proof that the network fails or that sub-300 is
impossible, because the true worst-case `B` is unknown.

### What was computed

`d2_exact_closure.py` fixes a threshold `q` and tracks the exact integer defect
`D_t(v)` of every bag on the real `(3,3,2)` flow, using its ports, blocks and roles.
A sender is abstract: it may leak up to the bulk curve and the capture curve, chosen
worst-case. Exact sorts give zero defect everywhere, and `sum D = 0` is asserted at
every stage. An earlier float version broke that law at `D` near `1e24`, and the
imbalance faked a runaway, so defects are now integers.

The test is that every off-spine sender with at least 4000 columns keeps its mass
within its fringe. That size is where the curves were measured. Smaller bags are left
to T2.

### Exact role data

| Quantity | Value | Crude value |
|---|---|---:|
| `mid` fringe | 14.65 to 15.06 rows | 13 |
| `topRise` fringe | 15.6 to 16.1 rows | 13 |
| `botDesc` fringe | 15 to 247 rows | not modelled |
| `topDesc` fringe | 0, no up-port | not modelled |
| Feed into a child, rows per row of `B` | 0.507 (`mid`) | 0.5 |
| Mass gain per return to the same bag | 16 | 128 |

Evidence is `FlowDAG` at depth 20, model level. Note that `FlowDAG` defaults to
`Par(2,3,2)`, so `Par(3,3,2)` must be passed.

### The recurrence

A sender's one-sided escapes enter one end child, return two stages later, and the
bag has shrunk 16 times by then. At mass `i` rows this gives the steady fixed point

```text
i = feed*B_rows + 16*E(i, f),
```

so closure at fringe `f` requires

```text
B_rows <= B* = max_i (i - 16*E(i,f)) / feed.
```

Escapes can go deeper before returning. For a constant rate `e`, a stationary profile
`M_j(t) = 4^(-t) w^j` along the end chain needs `1/4 = e/w + w`, so `e <= 1/64`
(hand). This is the role-exact form of the old `1/128`, but it matters less, because
deep chain nodes hold tiny masses with small `E/a`. It was not seen numerically: depths
up to 22 are too short to show it. The attack curve sets the real limit.

### Result

| Method | Closing `B` in rows | Compare certified 17.7 |
|---|---:|---:|
| Simulator, depth 16, 24, 32, 40 | 16.10, 15.21, 14.99, 14.91 | 1.19 times too large at depth 40 |
| Steady formula, `f = 15` | 14.91 | agrees |
| One-sided adversary, depth 32 | 21.9 | weaker than the symmetric case |

Each simulator value comes from 11 sampled thresholds: cuts at levels 0 to 3 and
offsets from the root cut. It is not a maximum over all `q`, so it is an upper limit
on the closing `B`. The formula at `f = 14.65` gives about 14.3.

Capture slack is the largest multiple of the attack curve that still closes, at depth
32:

| `B` in rows | Largest capture multiple | Meaning |
|---:|---:|---|
| 17.7 | 0.56 | Below attack, so false for sampled scrambles |
| 14.2 | 1.12 | At the first-moment limit for bulk |
| 10 | 2.19 | |
| 5 | 4.88 | |

The attack curve, in rows of escape:

| `i` | `f=14` | `f=15` | `f=16` |
|---:|---:|---:|---:|
| 8 | 0.106 | 0.082 | 0.066 |
| 10 | 0.213 | 0.153 | 0.115 |
| 11 | 0.309 | 0.215 | 0.157 |
| 12 | 0.456 | 0.309 | 0.219 |
| 13 | 0.693 | 0.452 | 0.316 |
| 14 | 1.045 | 0.690 | 0.463 |
| 15 | 1.573 | 1.038 | 0.694 |

`n = 1000`, best of three seeds. These are lower bounds on the worst case. Pyramids
give an any-scramble floor at sparse mass, which the simulator applies.

### Can `B` move?

| Bulk value | Rows | Evidence |
|---|---:|---|
| Certified | 17.7 | `na_precision.py` |
| Needed at attack-level capture | 14.9 | this section |
| First-moment limit | about 14.2 | `d2_bulk_attack.py --limit`, heuristic |
| Random input | 1.8 | model |
| Best explicit attack | 1.9 | `d2_bulk_attack.py`, `n = 1000`, weak search |

Here the attack is far below the limit, unlike capture, where attack and limit agreed.
So the true worst-case `B` is between 1.9 and 17.7 rows, and this work does not
narrow it further. That gap is the one open question left in the route.

A union-bound proof has no room. Its best bulk (14.2 rows) leaves a capture multiple
of 1.12, on a curve already near its first-moment limit, while certified capture is
about 17 times above it (one-round 0.33 at `f = 13`, against attack `E/a = 0.0195` at
`f = 15`, `i = 11`; no two-round certificate exists at this mass). Reaching a smaller
`B` needs a bulk proof that is not a union over inputs.

### Fringe

| Fringe | 13 | 14 | 15 | 16 | 17 | 18 | 20 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `B*` in rows | 11.3 | 13.0 | 14.9 | 16.8 | 18.3 | 20.0 | 23.7 |

Each extra fringe row buys about 1.7 rows of `B`, so fringe 17 clears the certified
`B` at attack-level capture. Values at `f >= 17` use a six-point curve with two seeds.
No certificate slack is included, and a larger up-port has not been costed against
the schedule, whose `9/8` reserve argument assumes `pi/c = 15/4096`.

### New startup requirement

Stage 0 sends `n/8` wires to each child, so `B_rows` becomes `8*B_rows` in a 16-row
fringe. Closure needs a stage-0 leak of about 2 rows or less (hand, `16/8`, limit not
measured); the runs use 1 row, and 17.7 rows overflowed at stage 1 in a trace. The
crude closure missed this, because its feed is 0.5 and here it is 8. It is a one-off
depth cost, so it does not change the coefficient, but it is not proved.

### Limits

- The contract is worst-cased stage by stage. Escapes need not be jointly realizable
  across stages, so failure of closure means this proof shape fails, not the network.
- Sampled scrambles only, and curves come from `n = 1000`.
- Bags under 4000 columns, cut residuals after a cut freezes, and T2 are not covered.
  Residual at the end of a depth-32 run at `B = 2` rows was about 1000 keys.
- The bulk tail shape away from a cut is assumed exponential. It matters only for
  thresholds off a cut.

**Next decision.** Stop work on this stage and do not add Lean bridges for it. The two
options left are a non-union bulk bound, or a schedule with fringe at least 17 whose
reserves still close. Section 10 costs the fringe change and closes that option.

Reproduce with `python d2_capture_curve.py --out curve.json`, then
`python d2_exact_closure.py --depth 40 --attack curve.json --startup-bulk 1 --bisect`.

## 10. Fringe costing

**Verdict: no D2 schedule geometry under depth 300 gives a stable fringe large enough
to close.** Geometries with a bounded fringe all have a fringe near 15 rows, and all
fail closure at the certified `B`. Geometries with a larger formula fringe either drift
toward zero fringe with depth or have no valid flow. The fringe option from section 9
is closed for this schedule family.

### The fringe is set by geometry, not by the quota

For `Par(x,y,z)`, with `k = 2^x`, `A = 2^y`, `nu = 2^-z` and sender height
`m = 2^mu`, the up-quota is `(k*A*nu - 1) c / (k*A)^2`. Raising it raises the
children's up-flow, and so the parent allocations, in the same proportion. So for a bag
near capacity

```text
f = m (k*A*nu - 1) / (2 (k*A)^2),   feed = 1/(A*nu),   gain = 1/nu^2,
price = (x+y)/(x*z) * 3 * mu(mu+1)/2.
```

(hand.) For `(3,3,2)` at `m = 8192` this is exactly 15. No quota choice gives fringe
17 there, and `m = 2^14` costs 315.

### Flow check

The formula holds only while `a/c` stays bounded. `d2_geometry_scan.py` builds each
geometry under 300 on `FlowDAG` (sparse-bottom routing) and reports the worst `mid`
fringe among senders of at least 4000 columns. Evidence is at model level.

| Class | Geometries | Behaviour |
|---|---|---|
| Bounded | `(2,3,2)` 2^12, `(3,3,2)` 2^13, `(4,3,2)` 2^14 | fringe 13.5, 14.7, 15.3 at depths 10 and 20 |
| Drifts | every runnable `A=4`, `nu=1/2`, or `nu=1/8` geometry | worst fringe falls about like `1/d` |
| No flow | `A=2` with `nu=1/4`; most `nu=1/8` | conservation fails at the frontier |

Drift examples, worst `mid` fringe at depths 10, 20, 30, 40:

| Geometry | Price | Formula `f` | Worst fringe by depth |
|---|---:|---:|---|
| `(2,1,1)` 2^11 | 297 | 48 | 43.6, 27.7, 19.7, 15.3 |
| `(2,2,2)` 2^13 | 273 | 48 | 45.5, 26.0, 17.6, 13.3 |
| `(4,1,1)` 2^12 | 292.5 | 30 | 27.1, 22.6, 19.4, 17.2 |
| `(3,1,1)` 2^11 | 264 | 28 | 24.3, 18.4, 14.2, 11.9 |
| `(3,2,2)` 2^13 | 227.5 | 28 | 24.4, 16.9, 12.6 (depth 30) |

`(3,2,2)` matches the lemma in `D2-SPARSE-BOTTOM-300.md`, where `a/c` grows linearly
in `d`. The coefficient is asymptotic, so a fringe that falls with depth cannot close
at any fixed `B`.

The `A=2` flows break early. For `(2,1,2)` at 2^13, the worst `mid` allocation is
1.2, 1.8, 1.9, 3.3, 6.0 and 7.3 times capacity at stages 4 to 10. Its fringe falls
from 64 to 8.8 rows, and at stage 11 a `topDesc` node holds 6.1 times capacity with a
nonzero deficit, which the flow cannot route. So the formula fringe of 64 never
exists.

### Closure in the bounded family

`d2_exact_closure.py --params ... --rows ...`, attack-level capture, startup leak 1 row
(0.25 for `k = 16`):

| Geometry | Price | Closing `B` in rows | Certified `B` in rows | Miss |
|---|---:|---:|---:|---:|
| `(3,3,2)` 2^13 | 273 | 14.94 (depth 40) | 17.7 | 1.18 times |
| `(2,3,2)` 2^12 | 292.5 | 10.34 (depth 32) | 14.9 | 1.44 times |
| `(4,3,2)` 2^14 | 275.6 | 11.58 (depth 20) | 21.06 | 1.82 times |

Certified `B` at `n = 4000` columns by height: 2^9 8.83, 2^10 10.51, 2^11 12.51,
2^12 14.9, 2^13 17.7, 2^14 21.06 rows. `(3,3,2)` stays the closest case.

### What larger fringes would have bought

The attack curve near larger fringes closes up to about `f - 8` rows at gain 16:

| Fringe | 20 | 24 | 28 | 32 | 40 | 48 | 56 | 64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Closing incoming mass `i0*` | 12.3 | 16.2 | 20.0 | 23.8 | 31.8 | 39.8 | 47.7 | 55.8 |

At formula fringes, `(2,1,2)` 2^13 would allow capture 20.7 times worse than attack.
`(4,1,2)` 2^14 would allow 3.4 times, `(3,1,2)` 2^13 2.7, `(3,2,2)` 2^13 1.8 and
`(2,2,2)` 2^12 1.4. None of these fringes survives the flow check. The certified
one-round bound fails at all of them anyway: its best `i - 16E` is -26 to -61 rows,
because its entropy cost does not fall with the fringe.

### Limits

- Flow checks are finite depths, at most 40, and use only the `Par` family with its
  Chvatal schedule. A different schedule, port design or allocation rule is not
  covered.
- Attack curves at `f >= 20` use two seeds and `n = 1000`.
- The closure limits for `(2,3,2)` and `(4,3,2)` come from fewer depths than
  `(3,3,2)`.

**Next decision.** Inside the `Par` family, the sender-wide three-sort stage now
depends only on the true worst-case `B` at height 8192. Closure needs `B` at most
14.9 rows with capture at attack level, or about 10 rows with capture up to 2.2 times
attack. The best explicit attack reaches 1.9 rows, and the first-moment limit is
about 14.2. The decisive next step is a stronger bulk attack, or a structural lower
bound on `B`. If worst-case `B` is at least about 14.9 rows, this stage is dead for any
proof. If it is near the mean-field 2 rows, a non-union bulk bound plus a two-round
capture certificate within a few times attack is the route.

Section 11 takes this step.

Reproduce with `python d2_geometry_scan.py`, `python d2_geometry_scan.py --flow 2 1 1 11
--depths 10 20 30 40`, and
`python d2_exact_closure.py --depth 32 --params 2 3 2 --rows 4096 --attack curve.json
--startup-bulk 1 --bisect --bisect-range 6 22`.

## 11. True worst-case bulk leak at height 8192

**Verdict: narrowed, not closed, and the route is parked.** For sampled random
scrambles, the worst-case bulk leak lies between 3.79 rows (attack) and about 14.0
rows (the first-moment limit of a two-stage union proof, heuristic). So:

- The stage is not dead on `B`. The attack is 3.9 times below the 14.9 rows at which
  no proof could close it.
- No union proof saves it. Its best bulk value, about 14.0 rows, leaves capture a
  multiple of about 1.16 times attack, and capture's own union limit is about 1.3 to
  1.7 times attack at the masses involved.
- Closing needs a bulk bound of about 12 rows or less (rough interpolation), which
  must beat the union limit. Such a bound is a research problem in its own right: it
  is a maximum over correlated sums, like a spin-glass ground state.

### The exact decomposition

Fix a final half `T`. Middle column `v` then has a walk `W2_v`, and the final excess
on `T` is exactly `sum_v W2_v(middle_v)`. The leak therefore depends on two things:
how far round 1 can move each middle column, and how well that matches the walks.

Round 1 has one walk per input column. If cells landing in a middle half `S` are
priced +1 and the rest -1, every input column climbs its full walk. This is the move
the certified round-1 bound charges for, and it shifts `S` up and the rest down by
about 72 rows.

### Where the certified 17.7 comes from

| Round-1 middle spread (mean shift) | Rows | Evidence |
|---|---:|---|
| Typical half `S` | 71.7 | exact walk law |
| Attack, alternation | 75 to 81 | `n = 100` to 4000 |
| Attack, annealing over `S` | 95 | `n = 100` and 200 |
| First-moment limit, union over `S` | 122.8 | exact law, `d2_bulk_limits.py` |
| Certified (`na_precision.py`) | 192 | |

| Round-1 spread fed into round 2 | 80 | 95 | 123 | 141 | 192 |
|---|---:|---:|---:|---:|---:|
| Union over `T`, free middle, leak in rows | 11.16 | 12.21 | 13.99 | 14.89 | 17.44 |
| Typical `T`, free middle | 7.51 | 8.26 | 9.36 | 9.90 | 11.39 |

At the certified spread, round 2 reproduces the certified leak (17.44 against 17.7).
So `na_precision.py` is, in effect, a union over `T` given a round-1 spread of 192,
and that spread is 1.56 times its own union limit. A tight union certificate for
round 1 would give about 14.0 rows. Reaching 14.9 needs a certified spread of 141 or
less.

### Attacks on the full leak

| Attack | Leak in rows |
|---|---:|
| Random input | 1.8 |
| Single-window local search (section 9) | 1.9 |
| Two-level, `n = 1000` and 4000 | 3.2 to 3.7 |
| Two-level, then key-level polishing | 3.79 |
| Annealing the price set, `n = 200` / 1000 | 3.24 / 3.02 (from 2.38 / 2.83) |
| Ideal round 1 (any middle at spread 80), alternating `T` | 5.09 |

All are exact runs, so each is a lower bound on the worst case for its scramble pair.
The last row is not realizable; it bounds what perfect steering could add at the
attained spread. Attack values do not fall with `n` (3.69 at `n = 4000`).

### Limits

- Both first-moment limits treat columns as independent given the set. They are
  heuristic levels, not theorems, and the true maximum over sets lies between the
  annealed value and the limit.
- The capture union-limit ratios come from section 8 at `f = 13`.
- The 12-row threshold interpolates the capture-slack table of section 9.

**Next decision.** Park the sender-wide three-sort `(3,3,2)` stage. Both cheap
options are spent: no geometry under 300 gives more fringe (section 10), and no
union proof brings `B` low enough. Reopen it only with a structural bulk bound below
the union limit, for example one that controls the maximum over middle sets by
chaining or a second moment, rather than by a union. A tight union certificate of
round 1 alone (192 to 123) is a real improvement, but it cannot close the stage. The
coefficient is unchanged: best proved 789.75.

Reproduce with `python d2_bulk_limits.py`, `python d2_bulk_attack.py --columns 1000`
and `python d2_bulk_attack.py --columns 200 --anneal 8000`.

## 12. Spectral certificates of the bulk leak

**Verdict: the standard all-real-space spectral quadratic-majorant method cannot
meet the roughly 12-row closure target.** At 8192 rows and block size 64, exact
rational certificates give a lower bound of at least
`1132722958590345144049/78125000000000000000` (about 14.498854 rows) throughout
the rectangle `0<=mu<=2/15`, `0<=c0<=12`. The first-round certificate gives
per-side spread `D >= 90`. Outside that rectangle, `90*mu+c0 > 12` by the scalar
terms alone. Thus no choice of nonnegative `mu,c0` in this certificate class
meets the target. Floating point only proposes the rational witnesses; exact
integer diagonal-dominance checks verify them. This rules out the tested
certificate class for this stage, not the sender-wide network or other methods.
### The floor

Each column contributes `F(sigma) = max_k (x_k - mu k)`, where `x_k` is the walk's
prefix sum over `sigma` in `{+-1/2}`. A spectral certificate uses
`F <= sigma^T Q sigma + c0` on `R^K`. By the S-lemma this needs
`Q >= 1_k 1_k^T / (4(mu k + c0))` for every prefix `k`. Since
`lambda_max(sum_v Q_v)` is at least the average trace, the certificate is at least
`mu D + c0 + tr(Q)/4` per side of the walk. Weak duality bounds `min tr Q` below by
`(tr sqrt(Sigma_rho))^2` for any distribution `rho` over prefixes. Grouping rows
into blocks of `b` drops constraints, so every value below is a lower bound, and it
rises as `b` shrinks. This is the regime `n >> m`, where each walk visits distinct
columns.

The earlier floating-point table at this point is superseded. It sampled only a
coarse parameter grid and does not match the conservative exact continuous cover
above; use the rational certificate result and verifier as the current screen.
Block sizes other than 64 are not covered by that exact continuous certificate.
### Why it fails

A quadratic majorant has to dominate the walk at every scale at once, for every
`sigma` in the ball. It cannot use the fact that one `sigma` cannot be atypical at all
scales together, which the union bound gets from the exact walk-maximum law. That
costs a factor that grows with the number of scales, like the Rademacher-Menshov
logarithm, and the floor keeps rising as the grid is refined. Round 1, which has no
drift penalty, covers 12 octaves and is hit hardest.

### Limits

- The floor covers certificates that dominate `F` on all of `R^K`, with
  `lambda_max` of the summed forms. A degree-2 sum-of-squares certificate that uses
  the cube constraints `sigma_i^2 = 1/4` with prefix-dependent diagonal shifts is not
  formally excluded. A one-direction check shows a uniform diagonal shift does not
  help for `mu < 1/4`.
- Proofs that beat the first moment for such maxima are spin-glass interpolation
  (Guerra-type) or counting only locally optimal halves. Both are research problems,
  not certificates to compute.

**Next decision.** The exact screen rules out the standard all-real-space
quadratic-majorant rescue for the sender-wide stage. The stage itself remains
parked, not disproved: cube-constrained SOS bounds and other joint bulk/capture
arguments remain open. Current evidence favors searching for a different stage.
Best proved coefficient: 789.75.
Generate the continuous exact certificate from the worktree root with `python upper-bound/experiments/prefix-flux/d2_spectral_cert.py continuous --spread 90 --output ..\\..\\..\\LLM-helpers\\sub300-check\\artifacts\\sub300-structural\\prefix-flux\\d2_spectral_continuous_block64.json`; verify it with `python upper-bound/experiments/prefix-flux/d2_spectral_cert.py verify <certificate.json>`.

## 13. Boolean cube follow-up

The degree-two cube-aware SDP was screened after section 12. Its optimistic
one-direction, restricted-prefix relaxation reaches 15.15 rows at 24 blocks,
after continuously optimizing the drift and recomputing round-one spread.
This is numerical evidence only; see [D2-CUBE-SOS.md](D2-CUBE-SOS.md).
Higher-degree and joint two-round arguments remain open.
