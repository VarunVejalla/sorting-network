# Four structural experiments for a coefficient below 200

Author/signature: **GPT-6 (Codex)**. Date: 2026-10-14.
The exact serving variant and reasoning preset are not exposed in this session;
the signature deliberately does not invent an `astra-high` suffix.

Status: research proposals with conditional, unaudited mathematical derivations.
No new sorting bound, Lean proof, or numerical construction is claimed. The
accepted coefficient is 1419; 945 remains the conditional tapered target.
All logarithms and coefficient calculations below use base two.

## What was inspected and what changes

The source review included `best/AKS/Chvatal/PhysicalPack2.lean`,
`DepthSkeleton.lean`, `Bitonic/Net.lean`, `Sort/Untangle.lean`, and the live
`tapered-945` worktree's `AdaptivePaddedWitness.lean`, `GlobalFlowStep.lean`,
and `NOTES.md`. The requested old `tapered` worktree path is absent; the
registered branch/worktree is `tapered-945`. No changes were made there.

The three-sort node and its global repetition are the central obstacle.
The checked schedule charges `3d-21` ordinary nodes on `64^d` wires. The
tapered candidate retains the asymptotic price `T/2`, with node budget
`T=1890=3*630`. One retained depth-630 sort already contributes 315.
Thus even a free final repair cannot reach 200 while retaining those sorts
and that stage rate. The missing rank/frontier proof for 945 remains the
work of UB-22 through UB-24; none of the proposals here closes it.

Existing UB-14, UB-19 and UB-20 already cover final-sort repair, signed
transfer, and lateral attenuation. These four tickets change additional
parts of the algorithm: its persistent representation, its terminal
objective, its precision schedule, or the scope of its existence proof.
They are separate experiments, not four savings that can be added together.

My preferred first construction experiment is **UB-25**, paired with the
**UB-26** composition lemma. UB-27 has a cheap obstruction test and should
be screened before implementation. UB-28 is the highest-risk alternative.

## UB-25: persistent sorted packets, with merge-and-deal balancing

**Signature:** GPT-6 (Codex). **Priority:** P2. **Claim:** conjecture.

Replace the repeated destruction and restoration of column order by a
representation in which every live packet remains sorted. This is stronger
than UB-13's initial-run optimization: it changes the mixing operation
between sorts and requires packet order to survive the whole schedule.

Here is a specific local primitive. Take two sorted packets of length
`m=2^q`, merge them exactly, and deal the even and odd merged positions to
two output packets. Both packets are sorted. For every Boolean threshold,
if the input zero counts were `x,y`, the output counts are

```text
ceil((x+y)/2), floor((x+y)/2).
```

The same fixed network satisfies this identity for every threshold. Merging
two sorted packets by reversal followed by bitonic merge costs at most
`q+1` binary layers; a full fresh packet sort costs `q(q+1)/2`.
`Bitonic.bitonicMerge_depth_le` is present in the source; the merge-and-deal
adapter and its correctness are new obligations. Fixed reversal/dealing
must be tracked as wire layout, with an eventual application of the
existing untangling theorem. They are not input-dependent routing.

Apply this operation in a fixed sequence of matchings of the packets.
This gives an actual comparator realization of rounded averaging, rather
than an input-dependent balancing assignment. It also gives a useful
deterministic first screen, with no union over input profiles:

* Let there be `c` packets. Replace each rounded averaging step by its real
  pair-averaging matrix `A_j`.
* Suppose a cycle of `s` such matchings has product `P=A_s...A_1` with
  Euclidean operator norm at most `rho<1` on the zero-sum subspace.
* Each rounded step has zero-sum error of norm at most `sqrt(c)/2`.
  Averaging matrices are nonexpansive. Therefore, after `t` cycles, the
  vector `x` of zero counts, with conserved mean `h`, obeys

```text
||x-h*1||_2 <= rho^t * m*sqrt(c)/2
                 + s*sqrt(c)/(2*(1-rho)).
sum_j |x_j-h|/(m*c) <= rho^t/2 + s/(2*m*(1-rho)).
depth of the cycles <= s*t*(q+1).
```

This derivation uses the variance bound for numbers in `[0,m]`, the triangle
inequality, and a geometric sum. It is a conditional hand calculation,
not a certified mixing construction. For a threshold with `pc` zeros,
sorted packet columns have `sum_j (x_j-p)_+` misplaced zeros beyond row `p`;
because the deviations sum to zero, this is half the displayed L1 error.
Non-row-aligned cuts require an additional partial-row allowance.

This exposes both the opportunity and the limits. Uniform bulk mixing can
be proved from a deterministic matrix inequality, without exact random-row
sorting or a fresh adversarial union bound. But the rounding floor is real,
and L2 mixing alone does not give the required multiplicative rare-cohort
contract. Do not use this as a drop-in proof of today's Property F.

The major global question is how packets survive the output ports. Balanced
columns contain the whole rank range: sending whole columns to children
does **not** partition the ranks. Row-slab ports instead cut each sorted
packet into sorted fragments. Splitting costs no comparisons, but restoring
packet height on receipt costs merges and must be charged. For example,
merging `2^b` equal sorted fragments of length `2^(q-b)` into one packet
costs at most

```text
sum_(j=1..b) (q-b+j) = b*q - b*(b-1)/2
```

layers using a balanced merge tree. For `b=6`, this is 195 at `q=35`, or
57 at `q=12`. It replaces one full sort only when those exact sorted-run
promises actually hold. Rare-fringe and frontier fragments can be ragged;
they do not automatically fit this formula. A single initial sort of
fixed-size packets is additive in n; any stagewise rebuilding is a leading
cost. Packet-aligned rounding, if used, costs O(m) wires per affected port
and must be included in the rank recurrence.

**First deliverable / early rejection gate.** Prove the merge-and-deal
count identity and obtain one explicit matching-cycle family, valid for
unbounded packet counts, with a certified `s,rho` and both a bulk and a
rare-cohort estimate. Search for a supported tail estimate using truncated
loads `(x_j-f)_+`, not just global variance. Then trace sorted packets through
one complete ordinary/frontier schedule cycle. A proof only for one finite
packet graph is insufficient for unbounded bag widths.

As an arithmetic gate, if the existing stage rate could be retained, then
`q=12` and 30 matching rounds cost 390 layers and price to 195 before any
repacking. With the ideal 64-fragment receive pattern, 26 rounds plus the
57-layer merge cost 395 and price to 197.5 before tail repair. These are
**budgets**, not proposed parameter tuples: no claim is made that either
round count meets a global contract. More plausibly this primitive needs
a new moderate-error scheduler or the localization objective in UB-26.
Reject the route if ragged fragments require unboundedly many merge levels,
or if certified mixing, tail repair and repacking cannot fit the full
global recurrence. Strongly nonuniform cohort inputs should be tested first.

## UB-26: power-scale localization and recursive exact cleanup

**Signature:** GPT-6 (Codex). **Priority:** P2. **Claim:** conjecture for
the preprocessor; conditional hand derivation for the recurrence below.

Change the global target from zero outsiders at a fixed terminal scale to
an exact bound on the spatial extent of disorder. Seek one fixed binary
network `A_n`, depth at most `a*log n+O(1)`, such that for **every Boolean
input** its output is zeros, followed by an arbitrary interval of length at
most `b(n)=ceil(n^theta)`, followed by ones. The interval may depend on the
input; the network may not. This is a strong localization promise, not a
bound on the number or average displacement of wrong keys.

There is a useful, explicit cleanup lemma. Split positions into consecutive
blocks of length b. First sort disjoint pairs of blocks `(0,1),(2,3),...`;
then sort the shifted pairs `(1,2),(3,4),...`. Handle end blocks by padding
or restriction. An interval of length at most b meets at most two blocks,
and lies inside a pair in at least one pass. Sorting an interval cannot
disturb the zeros before, or ones after, the original Boolean dirty interval.
Thus if the first pass does not finish, the second does. Ordered comparators
preserve the sorted output once it is reached. The zero-one principle then
gives an exact sorter. Both passes cost depth; there is no free selection
of the pass or of the dirty interval.

The localized-disorder interface and overlapping-block idea are present in
[Dobrokhotova-Maikova, Kozachinskiy and Podolskii (2024), sections 4.2 and
4.4](https://kozmath.github.io/papers/upper_bounds.pdf). The proposed use here
is a **binary** preprocessor and a fully priced self-recursion, rather than
the independent binary compilation screened in UB-08.

There is a stronger interface worth testing first. Suppose the prefix
partitions the output wires into fixed consecutive blocks of length at most
`n^theta`, and each block carries a **contiguous interval of global ranks**
for every permutation input. Then recursively sorting every block in
parallel needs just one recursive level:

```text
F(n) <= P(n) + F(ceil(n^theta)),
P(n) <= p*log n + O(1),
limsup F(n)/log n <= p/(1-theta).
```

This rank-pure-block contract is stronger than s-sortedness, but is the
better target because cleanup does not double. To get below 200 it is enough
to build such a prefix with `p < 200*(1-theta)`; for `theta=1/4`, this is
`p<150`. Once the order of the rank intervals is proved, all block sorts
run concurrently and no cross-block merge remains.

The checked Chvatal network already has rank-pure final blocks of
`64^7=2^42` wires (`RealBlocks.realNets_purity` and
`RealBlocks.finalS_image_real`). Stop its prefix earlier so those blocks
have size `n^theta`: it uses `3(1-theta)log_64(n)+O(1)` ordinary stages,
each of depth 2838. This gives
`P(n)=1419*(1-theta)*log₂(n)+O(1)`, hence the recurrence above returns
exactly 1419. This source screen is useful because it rules out a tempting
shortcut precisely: early stopping the existing tree does not improve its
coefficient.

If no cheap rank-pure partitioner is available, seek only the weaker
s-sorted contract and use the overlapping cleanup route. Construct the
recursive sorting family at strictly smaller sizes, using exact base sorters
below a fixed cutoff. Its depth `F(n)` satisfies

```text
F(n) <= a*log n + O(1) + 2*F(2*ceil(n^theta)),    0 < theta < 1/2.
limsup F(n)/log n <= a/(1-2*theta).
```

The factor **2** is essential. This is a well-founded construction, not an
assumption of the desired sorter. Iterating the leading terms gives
`a*log n * sum_j (2*theta)^j`. At the base cutoff, the accumulated leaf
cost is of order `(log n)^(log_(1/theta) 2)`, which is sublinear in `log n`
when `theta<1/2`. Constant-factor padding and rounding have the same lower
order effect after enlarging the cutoff. A formal recurrence proof must
bound these terms, and cover all n, not merely a sparse subsequence.

| Localization exponent theta | Required preprocessing coefficient a for <200 |
| --- | --- |
| 1/8 | <150 |
| 1/4 | <100 |
| 1/3 | <200/3 |

For example `theta=1/4, a=90` would give 180 **if the preprocessor exists**.
Using the accepted 1419 sorter once for cleanup would instead cost
`90+2*(1/4)*1419=799.5`. The recursive self-improvement is the reason this
target is substantially less demanding than that one-pass calculation.

**First deliverable / early rejection gate.** Prove the two-pass cleanup
lemma and the all-n recurrence, then extract a localization-versus-depth
curve from a specified multiscale comparator construction. A concrete first
family is UB-25 packet balancing with a decreasing packet scale and fixed
overlapping block passes; both scaling and repacking must be priced. Another
source is a deliberately early-stopped tree schedule, but its remaining
outsiders must be localized, not merely few. Bound both far-tail occupancy
and the width of the resulting Boolean interval simultaneously for all inputs.
Reject any argument replacing interval width by total outsider mass, or
charging only one cleanup pass. A cheap localization preprocessor is the
open construction; the conditional recurrence alone improves no bound.

## UB-27: periodic precision restoration instead of uniform precision

**Signature:** GPT-6 (Codex). **Priority:** P2. **Claim:** conjecture.

Today's local contracts are strong at every active stage. Test a genuinely
different algorithm: `r-1` cheap, coarse stages followed by one strong
restoration stage. Allow a controlled transient error profile, certify it
over the entire period, and recover the original invariant only at period
boundaries. This is a time-dependent contract, beyond merely replacing
the scalar potential by the static profile in UB-19.

Normalize errors to the *current* capacities and derive actual affine
transfers `z' <= K_i*z+g_i` for each phase, including native-rank defects,
far outsiders and both orientations. The period map is

```text
K = K_(r-1) ... K_0,
g = sum_i K_(r-1) ... K_(i+1) g_i.
```

For a nonnegative envelope u, `K*u+g <= u` is one possible cycle-invariance
test. Every partial-period image must also stay inside the local providers'
cohort-support, port-capacity and rank-balance domains. A small spectral
radius for K alone does not bound the forcing or ensure those domains.
Terminal purity must hold at the actual stopping phase.

If, and only if, a period still advances `2r` input bits as in the intended
tapered stage rate, its coefficient is

```text
((r-1)*L + H)/(2*r).
```

The illustrative gate `r=8, L=64, H=1890` is `2338/16=146.125`.
There is no depth-64 stage or valid cycle map supplied here. This number is
an acceptance budget showing what could matter. If coarse stages stall the
frontier, recompute the denominator from the bits actually advanced. If
restoration needs several strong stages, charge each one. Full node sorting
or the existing separator cannot recover missing native keys from a
different bag; they are not automatically global reset operations.

**First deliverable / early rejection gate.** Work first with an idealized
strong stage that exactly sorts each current bag, on the actual fixed port
geometry. Can it restore a proposed envelope after several coarse routing
steps, even with zero local comparison error? Search adversarial signed
prefix profiles, especially the one-sided outsider displacement from UB-11.
If the required keys have left its causal/port reach, reject that period
design before searching for a coarse gadget. If it survives, derive a small
phase-indexed transfer and exact rational feasible envelope, then replace
the ideal reset by an actual priced network. The ideal test is necessary,
not a sufficient construction. UB-24 is required if reusing tapered flow;
an independent schedule must supply its own rank accounting.

## UB-28: certify an entire run through paired Boolean witnesses

**Signature:** GPT-6 (Codex). **Priority:** P3. **Claim:** conjecture.

Local universal separator certificates may pay for states that no single
input can realize at all stages of the chosen network. Explore selecting
all random matchings of the whole network at once, and proving directly
that no Boolean input leaves an output inversion. This changes the scope
of the existence proof; it does not assume the intermediate states are iid
or replace an adversary by a sampled input.

A precise witness language is available. A comparator is `(AND, OR)` on
bits. A certificate forcing an output to 1 follows both predecessors at
AND gates and one predecessor at OR gates; a certificate forcing 0 does
the opposite. Thus failure at neighboring outputs `i,i+1` is equivalent
to a pair of forcing certificates whose initial 1-leaf and 0-leaf sets are
disjoint. An input satisfying both exists exactly when those assignments
are compatible. Shared predecessors must be represented consistently;
treating repeated leaves or reused edges as independent is invalid.

The mathematical goal is an explicit finite bound

```text
sum_(adjacent output, compatible paired witness shape)
    Pr[that witness is realized by the random network] < 1.
```

Define the candidate family before counting: a descending dyadic scale
schedule, fixed even/odd neighboring block-pair passes at each scale, and
`d` independently chosen perfect cross-matchings per pair, with comparators
oriented toward the output order. Two passes per scale cost `2d` layers;
a fixed-size exact terminal cleanup is additive. `d<=99` is a sub-200
budget only for this two-pass schedule. Extra upward sweeps, scale repeats,
or terminal work change it. This family is a test object, not an assertion
that descending passes suffice; finding systematic counterexamples is a
valuable first outcome.

[Goodrich's Randomized Shellsort](https://ics.uci.edu/~goodrich/pubs/J-75.pdf)
is a source for multiscale randomized comparison schedules. Its stated
high-probability result is for each given input; it does not establish a
single choice sorting every input. A polynomial failure probability cannot
be union-bounded over all `2^n` Boolean inputs. Likewise the size result in
[Zig-zag Sort](https://arxiv.org/pdf/1403.2777), including its attenuator
contract, must not be treated as a logarithmic-depth theorem; the paper
explicitly distinguishes these quantities.

**First deliverable / early rejection gate.** Implement certificate
extraction on small candidate networks and compare it with exhaustive
Boolean failures or a SAT search for output inversions. Derive a counting
recurrence that prices both witness branching and collisions and remains
uniform in n. A compressed witness language that still has essentially
`2^n` choices may offer no gain; record that obstruction. Prove a whole-run
existence inequality before investing in expander certification or Lean.
This ticket supplies no such probability estimate yet.

## Completion criteria and relation to current work

| Ticket | New mechanism | First decisive evidence | Existing work it complements |
| --- | --- | --- | --- |
| UB-25 | Preserve sorted packets through mixing and routing | Priced merge-and-deal provider with tails and persistent packet invariant | UB-01, UB-06, UB-13, UB-20 |
| UB-26 | Recursively clean a power-size interval of disorder | Exact two-pass recurrence plus a cheap binary localization construction | UB-08, UB-19, UB-20 |
| UB-27 | Restore precision periodically | Feasible phase-indexed transfer including forcing and actual advancement | UB-19, UB-23, UB-24 |
| UB-28 | Global certificate for one complete randomized network | Uniform paired-witness counting inequality | Existing local profile-union investigations |

The author reviewed sources and derived the conditional formulas here;
the smaller ingestion agent only summarized existing notes and tickets.
Exact rational arithmetic checked the displayed depth gates. An exhaustive
Boolean screen checked the two-pass cleanup on 98,151 eligible `(input,b)`
cases for lengths 1 through 14, including truncated end blocks. This is
finite diagnostic evidence, not a proof of the all-size lemma. The ticket
registry is validated separately. No Lean build or contribution check was
run because there is no claimed sorting-bound contribution.
All four registry projections remain null. Any successful continuation
must prove an eventual all-n depth bound in the canonical model and pass
the contribution checks before changing the accepted coefficient.
