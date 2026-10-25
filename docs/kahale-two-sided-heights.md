# Two-sided certificate heights (LB-02)

## Verdict

Tracking zero **and** one certificate heights together, with every per-wire
constraint the Lean modules support, still has optimal rate exactly
`1/(1 - log2 phi) = 3.27056`. This holds for the histogram form and for the
positional form, including the active-comparator width restriction. The
kill test succeeds: one explicit schedule (Kahale's block-halving schedule,
with over-wide blocks left idle) meets all of the following at the
witness arity `N_d = floor(2^d / ((d+1) F_{d+1}))`:

- the zero-side requirements;
- the one-side requirements;
- the graded requirements on both sides;
- the width restriction.

This was checked exactly for every tested `d <= 1024`. The joint relaxation
cannot give anything above 3.2706.

The reason is structural. Every per-wire two-sided statistic is a function of
the wire's attainable rank interval. The zero-side and one-side requirements
bind on disjoint wire sets: the low-`z` wires are in the top `2^(s+1)`
positions and the low-`o` wires are in the bottom `2^(s+1)` positions. A
per-wire coupling could only bind where one wire must be small on both sides.
That needs `2^(s+1) >= n/2`, and there the requirements are vacuous.

## 1. The relaxation

**State.** Each wire `i` at time `t` (after `t` parallel stages) carries
`(z_t(i), o_t(i))`. The pair means that wire `i` has a zero certificate of size
at most `2^z` and a one certificate of size at most `2^o`. At time 0, every
wire has `(0, 0)`.

**Transition.** A comparator `(i < j)` acts as follows.

| Output | Zero height | One height |
|---|---|---|
| min output `i` | `min(z_i, z_j)` | `max(o_i, o_j) + 1` |
| max output `j` | `max(z_i, z_j) + 1` | `min(o_i, o_j)` |

The zero column is `Certificates.heightStep` (`certificateHeights_correct`).
The one column is its order dual. It is valid by
`one_certificate_min_append` / `one_certificate_max_append` in
`CertificateCompatibility.lean`: the min output's one family is
`O_a ∩ O_b`, so a union of one certificate from each input is a one
certificate.

**Constraints.** These are necessary for a `d`-stage sorting network from
which redundant comparators have been deleted. Below, `s = d - t` is the
number of stages remaining.

- **(Z)** `z_t(i) >= s+1` for every `i >= 2^(s+1)`. This is Kahale's
  condition, `selection_certificate_height`.
- **(O)** `o_t(i) >= s+1` for every `i < n - 2^(s+1)`. This is the order
  dual.
- **(G)** Graded form, for every `h`:
  - zero side: `z_t(i) >= h+1` whenever `i >= 2^h + 2^s`;
  - one side: `o_t(i) >= h+1` whenever `i < n - 2^h - 2^s`.

  Taking `h = s` gives (Z) and (O). The zero side follows from
  `Fanout` (`ApproxSelect pre t 2^s` holds for **every** `t`) plus
  `RankInputs` (`SelectZeros`), applied at `t = 2^h` rather than `2^s`. At
  `s = 0` this is the terminal threshold condition `|S| >= i+1`,
  `|T| >= n-i` (`sorts_iff_certificate_card_bounds`).
- **(W)** A comparator followed by `s'` later stages has
  `j - i <= 2^(s'+1) - 1` (`ActiveWidth.active_comparator_width_le`). It
  holds for every comparator once redundant ones are deleted. Deletion
  preserves the function, because a redundant comparator is the identity on
  every vector that reaches it.
- **(C)** The coupling `z_max + o_min <= n+2`
  (`active_comparator_union_cost_coupling`) and its single-wire form
  `|S| + |T| <= n+2` (`rank_threshold_certificate_pair` with `i = j`).

(C) bounds certificate sizes from above, just as heights do. Requirements
(G) give lower bounds, at most `(i - 2^s + 1) + (n - i - 2^s)`, which is
`n + 1 - 2^(s+1)`. So (C) never conflicts with them. Its only consequence for
the rate question is the width restriction: combining (C) with (G) at the
comparator's outputs yields `j - i <= 2^(s'+1) + 1`. (W) is the sharper
checked form of that consequence.

**Exact meaning of the two sides.** Let `[lo, hi]` be the attainable-rank
interval of a wire (`RankInterval`). Then:

- the minimum zero-certificate size is exactly `lo + 1`;
- the minimum one-certificate size is exactly `n - hi`.

The `lo + 1` claim holds in both directions. A size-`k` certificate made into
the `k` lowest ranks forces rank `< k`. Conversely, the lowest `lo + 1` ranks
form a zero certificate. The one side is dual. So the per-wire two-sided
information is precisely the rank interval, and (G) says that interval lies
in the window `[i - 2^s, i + 2^s]` (Kahale's rank cover). Heights are the
closed-dynamics upper bounds on the endpoints `lo` and `n - 1 - hi`. The
interval itself has no closed per-wire update: the min output's `hi` depends
on the joint law of the two inputs.

## 2. Rate of the histogram form

Drop positions. The relaxation then asks for a schedule whose joint
histogram satisfies the counting forms
`#{z <= s} <= 2^(s+1)` and `#{o <= s} <= 2^(s+1)` at `t = d-s`.

- **Upper bound.** Projecting to `z` gives Kahale's zero-only system. So
  every feasible `n` satisfies
  `n <= U_d := min_s 2^(d+1)(s+1) / C(d-s, s)`. This is the kernel-checked
  inequality.
- **Lower bound.** Use equal-`z` pairing: equal `(z, o)` pairs first, then the
  leftovers of each `z`-class in `o` order. Exact big-integer simulation
  passes both sides at `n = N_d` for
  `d = 32, 64, 128, 256, 512, 1024`. The worst count-to-budget ratio is
  `<= 1/2` on both sides.

`log2(U_d / N_d)` takes the values 11.5, 13.8, 16.3, 18.8, 21.2, 23.7 at
those depths. That is `~2.45 log2 d`, a polynomial gap. Both
`d / log2 U_d` and `d / log2 N_d` converge to the same constant. The joint
optimum `n*(d)` lies between them, so its rate is **exactly** `3.27056`. No
exact optimum `n*(d)` was computed, and none is needed for the rate.

**No new eigenvalue.** Under equal pairing, `(z, o) -> (z, o+1), (z+1, o)`.
Up to idle rounding, the joint law is `(B, t - B)` with
`B ~ Bin(t, 1/2)`. The joint transfer operator is the scalar one with `o`
slaved to `t - z`. Its zero and one marginals are mirror images, so the two
counting constraints are the same inequality,
`n C(d-s, s) 2^-(d-s) <~ 2^(s+1)`. Hence the same Fibonacci/golden-ratio
exponent.

## 3. Kill test: positional, mirrored, width-restricted

**Schedule.** This is the block-halving schedule of
`kahale-positional-barrier.md`. Zero heights stay sorted; a block of `m`
equal-`z` wires pairs `(b+k, b+ceil(m/2)+k)`. It now also tracks one heights.
Variant `--skip-wide`: a block whose halving width `ceil(m/2)` exceeds the
(W) bound for that stage idles for that stage.

**Results** (exact; full output in
[`kahale-two-sided-heights-output.txt`](kahale-two-sided-heights-output.txt)):

| `d` | `log2 N_d` | `d / log2 N_d` | Z | O | G (both) | W, plain | wide blocks idled |
|---:|---:|---:|:-:|:-:|:-:|:-:|---:|
| 40 | 7.3 | 5.46 | ok | ok | ok | fails | 26 |
| 64 | 14.0 | 4.57 | ok | ok | ok | fails | 149 |
| 96 | 23.2 | 4.13 | ok | ok | ok | fails | 466 |
| 128 | 32.6 | 3.93 | ok | ok | ok | fails | 955 |
| 256 | 70.7 | 3.62 | ok | ok | ok | fails | 4695 |
| 512 | 148.0 | 3.46 | ok | ok | ok | fails | 21186 |
| 768 | 225.7 | 3.40 | ok | ok | ok | fails | 49227 |
| 1024 | 303.6 | 3.37 | ok | ok | ok | fails | 88746 |

How to read the table:

- The Z/O/G columns are for the `--skip-wide` schedule, which satisfies (W)
  by construction. The plain schedule also passes Z/O/G but violates (W).
  For example, at `d = 40` it has 181 of 3013 comparators too wide.
- `d / log2 N_d -> 3.27056` slowly, because of the `(d+1) F_{d+1}`
  normalisation.
- **Control.** At `d = 64` the skip-wide schedule still passes everything at
  `128 N_d`. At `256 N_d` it fails (O) and (G-one) but not (Z). So the checks
  are not vacuous and the witness is within a polynomial factor of `U_d`.
- The run-length implementation (`rle`) agrees wire-for-wire with the
  per-wire implementation (`pos`) at `d = 56`, in both modes.

**Why idling wide blocks is free on the zero side (all `d`).** Consider
stage `t+1` with `s = d - t` stages remaining. (W) allows width `2^s - 1`, so
an idled block has `m >= 2^(s+1) - 2`. The rounding bound gives
`#{z_t <= s} <= 2^s + s + 1 < 2^(s+1) - 2` for `s >= 3`. The cases
`s <= 2` are covered by the exact runs. So an idled block has
height `>= s+1`, and every later (Z) requirement is `<= s`. The counts
`c_h(t+1) = ceil(c_h / 2) + floor(c_(h-1) / 2)` for `h <= s` involve only
blocks of height `<= s`, so they are unchanged by idling higher blocks. Hence
(Z) for the skip-wide schedule follows from (Z) for the original schedule,
which is proved in `kahale-positional-barrier.md`.

The one side, (O) and (G-one), is verified only numerically. The schedule is
not exactly self-dual: an odd block's idle wire sits in its lower segment.
Per-wire `z + o` falls up to 61 below `t` at `d = 80`, so no per-wire identity
gives (O). An all-`d` proof would need a dual count bound for this schedule,
or an exactly self-dual schedule. Since the result is a barrier, this is
bookkeeping, not a gap in the conclusion.

**The barrier, precisely.** For every tested `d <= 1024` there is a `d`-stage
comparator schedule on `N_d` wires whose two-sided heights satisfy
(Z), (O), (G) and (W), and therefore (C) in the only form it constrains. So
no argument that uses only per-wire certificate-height pairs, the threshold
or window requirements, the `n+2` coupling and the active width can force a
coefficient above 3.27056.

The 161-wire defect (a zero certificate of size 77 and a one certificate of
size 65, disjoint, on middle wires 85/86) is invisible to every such
statistic. Those wires have heights near 20, so `2^h >> n` and the height
bounds are vacuous there. The defect is the disjointness of two certificates
on two different wires, which is a cross-wire fact.

## 4. What would be needed for 3.5

The coefficient sets the required gain. With `n F_{d+1} <= 2^((1-delta) d) poly(d)`:

- coefficient 3.5 needs `delta ~= 0.0200`;
- coefficient 3.3 needs `delta ~= 0.0027`.

That is an exponential-rate loss. Per-wire two-sided data cannot supply it
(section 3). A constraint that could must be **cross-wire**:

1. **Pair disjointness statistic.** For wires `i <= j`, let
   `D_ij = min{|S| + |T| : S in Z_j, T in O_i, S ∩ T = ∅}`. Sorting is
   exactly `D_ij = ∞` for all `i <= j`
   (`sorts_iff_certificates_intersect`). Comparators update it through the
   exact family rules: union, intersection, and the inclusion-minimal unions.
   This is the LB-24 pair-union state. The new requirement is a *rate*
   statement: in the last `~0.9 log2 n` stages, each stage can raise `D` to
   `∞` on only a limited set of pairs. Kahale's extremal schedule needs
   `~n` middle pairs closed within the binding window.
2. **Proof structure** if (1) yields a pair inequality. The pieces are:
   - (a) a closed upper recurrence for a pair potential (the LB-24 recurrence
     is a start);
   - (b) a per-stage growth factor `< 2^(1-delta)` on that potential for
     schedules that satisfy the per-wire constraints above;
   - (c) the endpoint value forced by `sorts_iff_certificates_intersect`.

   The Lean work beyond the existing modules:
   - the order-dual of `Certificates` and `SelectionCounting` (one heights,
     `SelectOnes`);
   - the graded `selection_certificate_height` at `t = 2^h`, a one-line
     generalisation;
   - redundancy deletion (removing redundant comparators preserves `exec`);
   - the pair recurrence and its growth bound, which is the real content.

Recommended next step: stop per-wire LB-02 work. Move to LB-24, the pair
union costs. Its first test is whether the skip-wide schedule above violates
some cross-wire `D_ij` growth bound at an exponential rate. Small `d` with
exact families is feasible with `kahale_certificate_probe.py`-style code.

## Reproduce

```sh
cd lower-bound/experiments/scripts
python -B kahale_two_sided_heights.py hist 32 64 128 256 512 1024
python -B kahale_two_sided_heights.py rle 40 64 96 128 256 512 1024 --skip-wide
python -B kahale_two_sided_heights.py rle 64 128 256          # plain: W fails
python -B kahale_two_sided_heights.py pos 40 64 96 --skip-wide   # per-wire cross-check
python -B kahale_two_sided_heights.py rle 64 --skip-wide --scale 256  # control: O fails
```

These are finite exact computations of a relaxation. They make no sorting
claim and add no Lean.
