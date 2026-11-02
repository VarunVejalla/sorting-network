# D2 spatial invariant: exact statement and first gate

Status (2026-11-01): the gate **fails** for the stage network formalized so far.
No spatial invariant can hold for it on arbitrary inputs. Section 4 states the
invariant for a bag-wide stage network, which is the form that can still hold.
That form is a specification only: its provider does not exist yet.

Evidence labels: **hand** (short argument given here, not kernel-checked),
**model** (exact finite computation), **crude** (order-of-magnitude budget).

## 1. Setting

Let `n = 8192 * 8^d` and `T = 262144`. The wires are addresses `0..n-1`. For
stage `t` and tree node `v`, `S_t(v)` is the sender set, and `native(v)` is its
address interval. `D2-DYNAMIC-SENDER-SETS.md` defines the routing: sets are
actual wire indices, with no wire permutation, and output slots are ordered by
increasing address.

The formal stage is `reflectedSenderFullTileStageNet` in
`D2ClippedCellRankInterval.lean`. It runs the core independently on consecutive
`T`-wire rank tiles of a sender, and comparators exist only inside a tile.

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
- Root mass after stage 0 is only `n/240` for `(3,3,2)`, and `n/120` for
  `(3,2,2)`. So the zero is not an accident of alignment that a shifted tiling
  would repair: shifting would still allow at most one straddling root tile per
  stage, which is at most `T/2` keys per stage against the `n/2` needed.
- `wire_partition_check.py --compressed` confirms routed sets equal static bags
  (rerun at depth 20; 32,750 routing cases). Earlier runs reached depth 120.

**Consequence.** Take the input with all false keys on the upper half of the
addresses. It needs `n/2` keys to cross `m`, and none do. Any completion would
need the cleanup to move all of them, so the cleanup would itself be a full
sorter. Depth 276 buys nothing here.

For a general cut the same argument applies through the cut's ancestors: at most
one straddling tile per ancestor per stage. That is `O(log^2 n)` keys in total,
so the network can only repair inputs whose cut defects are already that small.

The premises are checked at finite depths, not all depths. The conclusion is
about this construction, not about D2 schedules in general.

### Why earlier gates did not show this

- `D2GeometricProfileBudget.lean` assumes `error 0 <= 512 * tiles 0`. On the input
  above the root has parent discrepancy about `n/2`, while `512 * tiles` is
  `n/512`. The premise is false at startup for arbitrary inputs. The theorems are
  sound; their hypothesis is never supplied.
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
`(3,3,2)`.

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
band on a large bag. The provider must be sender-wide. By section 2, any
provider built from disjoint address-consecutive pieces fails, whatever the local
quality. Scattered pieces are not excluded by section 2, but each such piece then
acts as one column, and a single column pass gives no separation.

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

- **Startup.** Immediate from fact 1. The envelopes must only be nonnegative.
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

### First budget check (crude)

Capacity is `cap(i,t) = N * A^i * nu^t / (A*nu*k)` with `A = 8`, `nu = 1/4`, so a
child at time `t` is 32 times `cap(i,t+1)` and a parent is 1/2 of it. Take
geometric envelopes `delta^r * cap`, with up-ports passing all strangers and a
fraction `eps` of the parent's strangers escaping capture. Closure needs

```text
256*delta + eps/(2*delta) <= 1.
```

With `delta = 1/512` this needs `eps <= 1/512`. The end-port fraction is only
`pi/c = 1/256`, so about `1/512` per end. Thus the provider would need to catch all
but about `1/512` of a bag's extreme strangers in a fringe of about `1/512`, which
is 8 rows at height 4096. With `eps = 1` no `delta` works (the left side is at
least `2*sqrt(128)`). This is the same fringe question that the fixed core was
adopted to avoid, and it comes back unchanged.

## 5. What survives

| Work | Status after this gate |
|---|---|
| Abstract flow, reserves, port grid, dynamic sets, routing | Valid schedule facts, independent of the provider. |
| Fit and static-bag work | Needed for O1 and T1, not made redundant by dynamic sets. |
| Fixed core, 448 transfer, tile aggregation | Sound, but only relevant to near-sorted inputs. Not a route to the startup hypothesis. |
| Block-and-seam cleanup | Valid and reusable for T2. |
| Coefficient 230 | Withdrawn for `(3,3,2)`; see section 3. |

## 6. Next gate

Do not add Lean bridges to the tile-scatter stage. Decide the provider first:

**Claim to test.** There is a sender-wide network of depth below 300 per stage on
`(3,3,2)` (or below 360 on `(3,2,2)`, at rate `5/6`), with cleanup still to be paid
from either budget, satisfying `Sep(tau)` with `eps` near `1/512` at a fringe near `1/512`, for
all sender sizes.

**Rejects the route** if the available row-scramble tail bounds at height 4096 miss
that target by a clear factor, using the existing R1 and F2 tooling and the
recorded fringe screens. **Passes** only if a certified tail meets O2 and O4 at the
actual role quotas. An independent review of section 2 should come first, because
it reverses the route's standing assumption.
