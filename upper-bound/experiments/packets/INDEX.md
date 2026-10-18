# UB-25 packet work: current map

**Claim status:** no improved global sorting bound is proved. The verified
endpoint remains `limsup D(n)/log2(n) ≤ 1419`. The near-200 figures below are
conditional cost budgets, not theorem statements.

**Current cost screen:** the conservative direct-composition screen is about
240.5, conditional on two bits of progress per stage and still excluding
physical reblocking and terminal cleanup. The 195 sub-200 screen uses 15 local
and 9 global rounds plus a 78-layer block sort; it requires the unproved
coarse/fine cross-map bounds of at most `383/1000` in the stated compatible
decomposition, as well as a repeatable physical stage and a terminal sorting
argument. Treat 195 as the target budget, not the current candidate's bound.

**Source status:** `PacketReceiverOverlap.lean` has been restored as readable
Lean source and committed in `3ad4813`. Its restored support-sort and receiver
partial-group results were rechecked with the focused command recorded below.
The earlier truncation/recovery note is historical and no longer describes
the worktree.

**Stage specification:** [`STAGE-SPEC.md`](STAGE-SPEC.md) records the most
concrete candidate stage, its depth ledger, the unresolved output-to-next-stage
map, and the terminal sorting criterion. The candidate is not yet a complete
repeatable network: the missing map and terminal criterion are explicit
research gates, not implicit zero-cost steps.

## Candidate algorithm

Maintain a family of sorted packets through the repeated `flowA7` stages.
At a receiver, the checked selector decomposition gives up to 129 regular
rank-cell streams (one parent and two per child) and at most 65 endpoint
packets. Group each regular stream into consecutive 4096-wire blocks; pool the
stream residues and endpoints (at most 8,192 64-wire packets, hence at most
128 more 4096-wire blocks). Sort each block by a 57-layer merge tree. The
separate mixing proposal applies a fixed sequence of merge-and-deal matchings
to reduce packet-profile error. This is not yet a repeatable algorithm: the
matching schedule, the placement of its output packet IDs into the next
receiver state, and the target-profile update have not been coupled.

Representation constraint: a scattered sorted logical run cannot be made a
physically sorted run by a free wire renaming. `ComparatorNetwork.scatterEmbed`
is proved only for an order embedding; an arbitrary embedding can reverse a
comparator (already on two wires, the reversed embedding asks for a descending
comparator). Thus the next stage must either receive rank cells in increasing
physical order or pay for a real repair network. Support equality of a 4096
block alone does not provide this order-preserving cell crosswalk.

There is a generalized-network nuance: `Untangle.untangle` converts a
generalized network that sorts *all inputs* in a specified output permutation
to a standard sorter at exactly the same depth. It does not automatically
apply to the merge tree here, whose correctness assumes 64 sorted input runs;
the theorem's all-input premise is absent. A restricted-input untangling lemma
that fixes the desired physical output order would be a useful route to test,
but until it is proved, it cannot be counted as a zero-cost alignment step.

The worktree README's final proof step already uses `Untangle` on the full
generalized network. That can avoid requiring every intermediate packet round
to preserve physical order, provided the whole construction has an all-input
sorting proof and each return to `WireFlow` restores rank-cell sortedness.
Neither the all-input recurrence nor that repeated reblocking contract is
proved; this does not remove the target-coupling or coarse-mean gates.

Same-cost physical-sort option: a bitonic sorter on 4096 wires has depth 78,
equal to the current `21+57` local-sort/merge reassembly budget. Replacing
that reassembly by a full 4096-wire sort on each exact rank-block support
would therefore keep the conditional 14-local/10-global coefficient at 195,
not raise it to 234. It would make each block physically sorted in its
canonical support order. This is a viable local substitution to test, but it
does not order distinct blocks relative to one another, align the pooled
endpoint/tail packets, or establish that the next `WireFlow` stage may use
these blocks as its source bags. The 15-local-only budget similarly remains
136.5, with the coarse-mean contraction still unproved.
The local network is now kernel checked as `bitonicSort4096OnSupport` in
`PacketReceiverOverlap.lean`: depth at most 78, sorted on the support's
increasing enumeration, and unchanged outside the support. The actual batch
instantiation and complete receiver partition are still open.

## Checked components

- The 64-wire odd-even merge sorts two sorted 32-wire runs in six layers;
  the arbitrary-support merge-and-deal adapter is checked at seven layers.
- A merge tree sorts 64 disjoint sorted 64-wire packets into a sorted
  4096-wire block in at most 57 layers. Receiver-local and global one-stage
  support partitions/batches are checked, including root handling.
- Actual interior receiver selectors are split into 129 disjoint regular
  streams and a concrete sorted exception pool. Each regular stream is
  grouped into full 4096-wire blocks plus its residue. The guarded theorem
  `flowA7_receiver_regular_partial_groups_sum_le_258` proves at most 258
  partial regular groups per receiver rank interval. This is a support
  incidence bound, not a profile-error bound. The latest recorded focused
  Lean check for this receiver/profile cluster is
  `check-lean.ps1 -From PacketInduction -To PacketMergeAxioms`.
- `wireFlowLayer_reencoded_profile_energy_recurrence` and its squared-error
  form transport a coherent monotone threshold target through one actual
  `WireFlow` layer; the squared-error bound has factor 65. Pair merge-and-deal
  energy lemmas handle moving targets when the output target is the average of
  the input targets. The missing bridge is showing the actual routed target
  obeys that average law, or bounding its drift.
- If one matches equal-index blocks across the at most 129 regular streams
  plus one pooled exception-block stream, matching fan-in is bounded by 130
  even though each stream may be long. `bounded_fanin_cycle.py` exactly
  verifies in Python a 15-round cycle for every fan-in `c=1..130`, with
  Frobenius (hence spectral) norm at most `1/16`.
  This would make the factor-65 energy recurrence contract by at least
  `65/256`, conditional on that being the actual packet-ID schedule. The
  certificate is not Lean-checked and does not prove the schedule is repeatable;
  the incomplete exception-pool tail remains outside this matching screen.
  Rechecking the exact stored matrices gives a sharper worst squared
  Frobenius bound `rho^2 = 804287/268435456` (fan-in 125). The generic
  overlap-L2 lemma would therefore contract the fine error if the actual
  reblocking had at most 258 nonzero source-block errors per destination:
  `258*rho^2 = 103753023/134217728 < 1`. The checked 258 partial-group
  incidence theorem is not yet this overlap bound, and cohort-constant means
  remain untouched by the local matching cycle.
- Frontier error terms have separate checked local bounds. Their startup and
  termination charges are not yet included in a closed recurrence.
- `integer_matching_state_screen.py` simulates the exact integer count update
  for a fixed matching cycle. It confirms strong finite mixing on dense inputs
  and no L1 contraction for a single one; it is a local matching screen, not a
  full `WireFlow` scheduler simulation. See `MIXING-TAIL.md` for results.
- The `flowSizes7` mid formulas yield a derived bag-constant transfer: one
  receiver takes weight `(64^4-1)/(64^6-1)` from its parent and
  `4095*64^3/(64^6-1)` from each child. This is near averaging over siblings,
  but does not cover rank-block errors or cross-stage contraction; details and
  the precise assumptions are in `MIXING-TAIL.md`.
- In the homogeneous mid-level tree model, the same weights yield a deep
  subtree cut with vanishing boundary-to-volume ratio. Local receiver mixing
  alone may therefore fail to contract coarse modes uniformly; the actual
  frontiers and any global cross-subtree schedule must be included to decide.
  The eight-round abstract matching-family gate now has a nonconstructive
  asymptotic route: strong convergence for independent random matchings and a
  Haagerup estimate give limiting centered norm `225/256`, hence existence of
  schedules with norm `229/256` for all sufficiently large even packet counts.
  This is an external-theorem research lead, not Lean checked, and does not
  establish the actual packet-ID transition or the coupled recurrence. Its
  contraction is not strong enough to cancel the factor-65 flow estimate:
  that naive composition needs 16 global rounds and costs 240.5.
  A possible two-scale route would need the combined coarse/fine cross-term
  operator below `27/256` in a compatible energy norm; this is only a target
  inequality, not yet a theorem.
- A sharper nine-round free-product calculation in `free_matching_bound.py`
  gives centered norm `11/16`, hence existential finite schedules of norm
  `45/64` for all sufficiently large even packet counts. In the same
  conditional two-scale model this raises the allowed combined coarse/fine
  cross-term norm from `27/256` to `19/64`. Its depth with 15 local rounds and
  78-layer reassembly is 195 per log bit (390 layers per two bits), leaving
  five units below 200. This remains conditional on the external asymptotic
  theorem and the unproved actual-state decomposition, target coupling, and
  rare-tail control.
  A sharper block-matrix test in `free_matching_bound.py` shows that, if the
  two cross maps are each bounded separately in the required orthogonal
  coarse/fine decomposition, `383/1000` per map suffices; this improves the
  simple additive `19/64` gate. It remains only a threshold—the actual cross
  maps and decomposition are unproved.
- `flow_subtree_cut_screen.py` uses exact rational `flowA7` formulas, including
  actual active frontiers, and verifies a level-6 descendant subtree loses
  only its root up-flow (`2.67e-51` of subtree mass at `d=t=40`). Its centered
  bag-density L2 ratio is at least `0.999999999992724`. This is not a packet
  profile realizability result; it rules out relying on `WireFlow` alone for
  uniform coarse-mode contraction.
- `global_matching_power_screen.py` tests global rounds numerically on
  packet sets through 65,536: sampled centered norm estimates stay near 0.21,
  and one-packet indicators contract to about 0.044. This supports global
  mixing numerically but does not certify an unbounded schedule family; the
  integer rare tail remains open. The asymptotic theorem route above now
  supplies abstract existence of a contracting family but does not remove
  these recurrence gaps.
- `random_compare_split_tail_screen.py` rejects a tempting tail repair: with
  uniform random perfect matchings, a singleton can reach the final ordered
  packet only by meeting that packet directly, so after `R` rounds the chance
  is at most `R/(C-1)`. A viable compare-split repair needs rank-aware,
  multiscale connections; this does not rule out expander or recursive designs.

Focused verification for the latest receiver-overlap and axiom-guard changes:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File upper-bound/experiments/packets/check-lean.ps1 -From PacketInduction -To PacketMergeAxioms
```

This passed, including the restored `PacketReceiverOverlap.lean` results and
the aggregate partial-group theorem. It does not rebuild the earlier merge
modules or check an end-to-end sorting bound. The first two bullets above
predate that focused range; no last-passing command for them is recorded here.

## Quantitative gates

The old headline `197.5` is `395/2`, where `395 = 26*13 + 57` layers assumes
26 merge-and-deal rounds on 4096-wire packets plus a 57-layer reassembly, and
assumes two bits of logarithmic progress per cycle. The new 15-round screen
would reduce this conditional budget to `(15*13+57)/2 = 126`, under the same
progress assumption. Neither estimate includes a proven repeatable schedule,
packet routing, or all correction costs. The independent review correctly
flags endpoint alignment as a missing, unpriced stage; a six-layer repair
outside reassembly gives `200.5` for the old 26-round budget, while the robust
21-layer local sorter gives `205`.

For the conservative rounded-cycle fresh-error term `s/(4m)`, `s=26` gives
`0.001587` per unit mass for `m=4096`, or about `0.156N` over 98 stages of
total active mass `N`. For `m=64`, it gives `0.1015625` per stage, or about
`9.95N` over 98 stages. These are different packet scales. The 4096-wire
term is still about 94,000 times the existing `1/59,000,000` Chvatal
allowance; reusing that kernel directly is not viable at this scale. A new
moderate-error recurrence would be needed.

Exact precision-versus-depth consequence (2026-10-18): with `s=26`, keeping
even this conservative *per-stage* term below the old allowance requires
`m >= 383,500,000`; the next power-of-two packet size is `2^29`. A merge-deal
round on sorted packets of that size has depth `log2(2m)=30`. At two bits of
progress per stage, 26 rounds therefore cost coefficient `26*30/2=390`,
before repair/repacking; 60 rounds cost `900`. This is a necessary scale
screen for reusing the old pointwise tolerance, not a lower bound on every
possible persistent-packet invariant. It explains why a viable sub-200 route
must prove a new moderate-error scheduler theorem, rather than merely improve
the matching contraction. The external review's roughly 60-round estimate is
consistent with this cost arithmetic but its contraction rate remains a
heuristic, not a certified uniform bound.

Reweighing the review's UB-26 fallback against the current local notes does
not supply that theorem. Early stopping the existing Chvatal prefix has no
physical dirty-interval guarantee and, even under optimistic rank-purity
assumptions, its cleanup recurrence does not beat 1419. The existing
row-scramble aggregate leakage contract does not imply a sparse exception
set, and no low-depth oblivious repair is specified. These are source-based
screens, not impossibility results for a redesigned UB-26 construction. They
do mean neither existing construction is a drop-in moderate-error cleanup for
UB-25. The relevant next result remains a one-stage, threshold-profile
recurrence for the actual packet scheduler, together with a sorting criterion
that accepts its resulting error and fits the depth budget.

The checked layer transfer costs factor 65 in squared error. Under exact
matching-target coupling, a matching cycle with certified energy contraction
`ρ²` gives factor `65ρ²`; the exact finite screen above has `ρ≤1/16`, so its
conditional factor is at most `65/256`. This is a promising fixed-fan-in
screen, not a proof of target coupling, packet-ID repeatability, or a formal
spectral certificate. The review's main go/no-go recommendation is adopted:
write and test the full recurrence before adding routing proofs. The 15-round
screen addresses only the matching contraction input to that recurrence.

For a centered error vector only, composing the checked factor-65 flow estimate
with that screen would give a conditional L2 recurrence if both act on the
same state and port transfer adds drift `δ_t`. The error must have zero mean
within every matching cohort; the constant mode is not contracted and must be
tracked separately. For total wire mass `N`, 4096-wire blocks, and `K≤N`
thresholds, the 15-round rounding term is at most `(15/128)N`:

```text
V_(t+1) ≤ (63/125) V_t + (15/128)N + δ_t,
```

where `V_t` is the centered L2 error and `65/256 ≤ (63/125)^2` certifies the
conditional contraction. The
`conditional_15_round_recurrence.py` exact-rational screen gives a zero-drift
steady-state bound `V/N ≤ 1875/7936 ≈ 0.2363`; a uniform drift `δ_t≤ηN`
adds at most `(125/62)η` to that bound. At 98 stages the initial-error term
is already negligible. This remains only a conditional centered-error screen:
the composition/state alignment, mean-mode evolution, port/target drift,
exceptions, and frontiers are unproved, as is sufficiency for final sorting.

A more promising two-scale state avoids composing the factor-65 theorem.
For each matching cohort, the exact certificate contracts only the centered
4096-block count-error vector: its L1 contraction is at most
`sqrt(130)/16 < 713/1000`. Fifteen rounds add at most `(15/2)` count-units
per block and threshold. The constant mean mode is preserved, so it must be
tracked separately. The abstract reblocking inequality is now kernel-checked:
`monotoneBlocks_assignedRankProfiles_L1_nonincrease` proves that arbitrary
reassignment of wires from sorted blocks to destination labels does not
increase aggregate L1 error when destination targets use the induced
suffix-interpolation. Its focused axiom guard passes. The actual `WireFlow`
66-piece sender interval owner map is also kernel-checked:
`wireFlowLayerPieceOwner_profileMean_eq_selected` identifies its induced
target with the actual selected-interval mean, and `wireSetPacketRankOwner`
assigns physical wires to their actual next registers. The new
`fourLaneBoundaryMatching_4096_rank_block` proves each grouped 64-output
support is exactly its 4096-wire support-rank interval and exposes the
grouped packet indexing. `fourLaneBoundaryMatching_4096Block_physicalSort`
now composes that identity with a 78-layer physical bitonic sorter, proving
sortedness on each exact block and its 64 constituent rank cells at the same
cost as the proposed reassembly. This establishes the local packet coordinates
for a full block. The remaining crosswalk is value/profile-level: identify the parity-lane
targets with the 66-piece intervals and include residues/frontiers. If centered error
survives this reblocking without an uncontrolled contribution `kappa_t`, the
fine-scale recurrence would be

The factor-65 flow energy estimate comes from Cauchy across the 65 source
bags of a receiver. Although selected sender-piece L1 errors are charged once,
their rank-profile errors can concentrate at threshold cuts; treating them as
uniform density and invoking mass-weighted Jensen would be unjustified without
a localization bound. The new kernel-checked
`wireFlowLayer_interior_source_error_mass_conserved` proves the sharper
source-side identity: each interior source's absolute cut-error mass is
routed once over its active receiver pieces. It does not control cancellation
between different sources at one receiver, which is exactly where the factor
65 enters. The recurrence must retain these source contributions by actual
4096-rank stream group through the matching cycle; the checked support bounds
give its fan-in, but not the error-vector/rank-block crosswalk. See
`MIXING-TAIL.md`.

```text
v_(t+1) ≤ (713/1000)v_t + 15/8192 + kappa_t,
```

where `v` is centered L1 error normalized by `N*K`, `K≤N`, and `N/4096` is
the block count. With `kappa_t=0`, its steady state is
`1875/293888 ≈ 0.00638`. The exact allocation screen in
`conditional_l1_cycle_recurrence.py` observes `3.94e-6 N` total unmatched
`<64`-packet tail wires through depth 80. A uniform geometric envelope now
proves this wire-mass charge is at most `N/86016` for every depth; it still
does not bound target-mismatch amplification or transfer from the uncontracted
mean mode. If each unmatched tail wire contributes at most one normalized L1
error unit, the conditional centered recurrence has limiting value at most
`22541/3526656 ~= 0.006392`; this sensitivity calculation is not a proved
tail-to-error bridge. A
receiver-rank window can be sorted in 78 layers (sort its 64 consecutive
64-wire cells in parallel at depth21, then merge the 64 sorted runs in depth57),
giving the raw conditional budget `(15*13+78)/2=136.5`. None of the L1
nonincrease, target compatibility, profile-error effect of tails, or final
sorting tolerance is proved. This is the leading structural route to test.

The independent review is at
[`LLM-helpers/reviews/ub-25-packets-review-2026-10-18.md`](../../../../../../LLM-helpers/reviews/ub-25-packets-review-2026-10-18.md), in the shared repository-root helper directory.
Its main recommendation—to settle the recurrence and precision-versus-depth
gate before extending routing plumbing—is adopted. Its `about 10N` stage-sum
calculation applies to `m=64`, not the preceding `m=4096` estimate.

Review disposition (2026-10-18): the review's old-kernel precision objection
and unpriced endpoint cost are confirmed by the exact scale audit above. The
proposed fanout-4, `m=16` simulation is not yet a meaningful scheduler test:
the checked transition still lacks the target/rank map that determines which
output packets enter each next-stage `WireFlow` cut. Simulating matching
rounds or an arbitrary rebinning would test a different process. Therefore
the next research gate is to derive the actual coarse target operator and its
coupling to centered error; only then should a scaled simulation instantiate
that same transition. The existing exact matching screens do not close this
gate. No new bound follows from the review or these calculations.

UB-26 fallback audit (2026-10-18): the separate .claude/worktrees/ub-26 screen confirms its seam-cleanup recurrence only conditionally gives C=(p+theta)/(1-theta) and the sub-200 gate p<200-201*theta. The existing Chvatal early-stop route is screened out: its rank invariant gives no physical interval, and even an optimistic width model costs above 1419. No screened Chvatal, row-scramble, direct-multiway, or high-arity reuse candidate supplies the required prefix. This rejects those reuse paths, not a new UB-26 preprocessor; defer formalizing cleanup until a prefix candidate plausibly meets the gate. See .claude/worktrees/ub-26/upper-bound/experiments/localized-cleanup/{STATUS,REUSE-SCREEN,PREFIX-SCREEN}.md.


Cut-map precision: the basic local rank geometry is already checked.
`senderOutgoingPiece_inter_portMacroGroup_eq` identifies each macroblock's
intersection with a next `WireFlow` sender piece as one explicit rank interval;
`flowA7_receiver_allCases_parityOwnerCount_intersection` gives the analogous
physical owner/count identity for parity lanes. What remains missing is the
ideal *profile target* on those intersections after merge, global matching,
and reblocking, and a proof that this target state repeats at the next stage.
Thus the full-scheduler simulation is blocked by target/state evolution, not
by the elementary support-to-owner map.

There is also a precise hypothesis gap in reusing the ordinary layer
recurrence: `wireFlowReceiver_register_count_error_reencoded` assumes each
entire source register has a monotone threshold profile. The packet invariant
currently gives sortedness only within its 64-wire cells (or sorted macroblock
runs), not across the whole register. The recurrence must therefore either
prove whole-register order at each handoff or retain packetwise target/error
profiles through the port split; a scalar register mean does not suffice.

The fine recurrence's missing mode is now stated explicitly in
[`MIXING-TAIL.md`](MIXING-TAIL.md): the stage transfer must contract cohort
means and bound conversion between mean and centered error. Only nine extra
13-layer rounds fit the raw `<200` budget. A floating-point screen of random
nine-round perfect-matching products gives centered norm about `0.20` for
256–2048 packets; this motivates testing a coarse expander schedule but gives
no uniform certificate or support-compatible `WireFlow` transition.

## Remaining gates, in order

1. **One repeatable stage:** define the packet-ID state and fixed matching / routing schedule; show the full output support partition, including endpoint and residue handling, is the one consumed at the next stage. The local macroblock-to-port interval and parity-lane owner maps are checked, but are not yet composed into this full repeated transition. Direct endpoint-pair rank alignment is disproved; do not pursue that invariant.
2. **Target coupling:** identify the routed `WireFlow` targets with the merge-and-deal matching averages, or prove a quantitative target-drift bound. Support alignment and conservation alone are insufficient; an abstract counterexample is formalized in `README.md`.
3. **Uniform error recurrence:** prove blockwise target transport and L1 nonincrease through port splitting/reblocking; incorporate the `<64`-packet tails and frontiers; then establish that the resulting `≈0.00638` normalized error is sufficient for the final sorting induction. The cycle screen includes fan-in through 130 (129 regular streams plus one full-exception stream) but omits the residual tail. The current local lemmas do not yet provide a closed all-level bound.
4. **Depth and theorem:** account for every mixing, merge, correction, and repacking layer; prove the all-`n` sorter bound and limsup theorem; run `upper-bound/TRUSTED.md` contribution checks.

## Detailed references

- [`README.md`](README.md): theorem map, target-mismatch witness, and proof commands.
- [`STATUS.md`](STATUS.md): dated formalization log; later entries supersede earlier ones.
- [`MIXING-TAIL.md`](MIXING-TAIL.md): rounding estimates, candidate aggregate recurrence, and scale audit.
- [`PacketMergeAxioms.lean`](PacketMergeAxioms.lean): explicit standard-axiom guards.

## Dyadic compare-split screen (exploratory, 2026-10-18)

The alternative UB-28 dyadic schedule now has a reproducible exact small-size
screen in [`dyadic_compare_split_screen.py`](dyadic_compare_split_screen.py).
At 16 packet IDs, five independently randomized cross-matchings per block
pairing pass give a sorting network for seed 500001, checked on all 65,536
Boolean inputs (40 comparator layers, 245 comparators). Seed 0 fails, with
profile `(0,0,0,1,0,0,0,1,1,1,1,1,0,0,1,0)`, so this does not support using
an unspecified/random seed as a construction. For eight packet IDs, seed
500001 also sorts all 6,561 profiles of packet zero-counts at capacity 2 under
the exact compare-split map
`(x,y) ↦ (min(m,x+y), max(0,x+y-m))`.

This is finite evidence only. It neither proves that a scalar sorting-network
topology lifts to sorted-run compare-splitters nor gives one uniform seed or
construction for every packet count. If a five-round schedule were proved for
all dyadic sizes and lifted to actual sorted packets, a packet comparator at
capacity `m=4096` costs 13 binary layers; two pairings at each scale would
then cost `2·5·13=130` per `log₂(packet count)`, before any initial finite
packet-sort overhead. The exact schedule is therefore worth pursuing as a
separate structural candidate, but it has not improved the accepted bound or
closed UB-25's recurrence, target-coupling, frontier, and end-to-end theorem
gates. The external review's advice to settle mathematical gates before
adding routing formalization remains applicable.

### Paired forcing-certificate interface

For a Boolean comparator circuit, let `P(w)` be the antichain of inclusion-
minimal input sets whose assignment to 1 forces wire `w` to 1, and `Z(w)` the
corresponding 0-forcing sets. With `Min` denoting inclusion-minimal members,
the exact backward recurrence at a comparator with low output `a∧b` and high
output `a∨b` is

```text
P(low) = Min { A∪B : A∈P(a), B∈P(b) }    Z(low) = Min (Z(a) ∪ Z(b))
P(high)= Min (P(a) ∪ P(b))               Z(high)= Min { A∪B : A∈Z(a), B∈Z(b) }
```

The network fails to sort iff some adjacent output pair `(i,i+1)` admits
`A∈P(i)`, `B∈Z(i+1)` with `A∩B=∅`: assign those disjoint certificates and
the outputs become `1,0`. The SAT screen now shrinks each failure model to
such a pair. For `n=64,d=7,seed=0`, it gives pair `(32,33)` with disjoint
inclusion-minimal certificates of sizes 31 and 29. This makes UB-28's
probabilistic gate precise: bound the chance/number of disjoint certificate
pairs under the random matching schedule, uniformly over dyadic sizes. Direct
antichain enumeration is already expensive at 16 wires, so a useful proof will
need a compressed statistic or a sharper recurrence rather than full families.
The reproducible SAT witness has 31 ones, 16 displaced ones from its sorted
threshold profile, and 38 input runs. The one-swap screen proves only that
this schedule has no failure at displacement radius 1; a radius-2 SAT check
timed out, so the minimum failure radius is unknown.

There is a potentially simpler sufficient target. If output `k` has no
1-certificate of size below `n-k` and no 0-certificate of size below `k+1`,
then it equals the `k`th sorted Boolean output: fewer than `n-k` input ones
cannot force it to 1, while fewer than `k+1` zeros cannot force it to 0.
Thus rank-correct minimum-certificate lower bounds at every output imply the
full sorting property. The `n=64,d=7` witness violates these already at the
center (`31<32` for output 32; its output-33 0-certificate has size `29<34`).
This rank-profile target may admit a smaller recurrence than counting every
disjoint pair, though certificate overlap still has to be controlled.

The single-swap test family does not explain the failures: the bit-parallel
screen `dyadic_single_swap_screen.py` checks all 43,680 single-swap profiles
for `n=64` and finds no failures for the tested schedules `(d,seed)=(5,500001),
(6,0),(7,0),(7,5),(14,0),(14,1)`. This is necessary evidence only; the `d=7,
seed=0` schedule still fails on the SAT witness above. Failure witnesses
therefore are not captured by one swapped pair across a threshold cut, which
is why a rank/certificate recurrence is still required.

As an ordinary comparator network on packet IDs, the schedule has `2*d`
layers per `log2(n)` regardless of packet lifting. The packet-lifted UB-25
implementation instead replaces each comparator by a 64+64 merge costing 7
layers, giving `14*2*7=196` for `d=14`. But the specific seed-0 schedule
fails at 128 IDs. The default SMT solver timed out as `unknown`; the SAT
tactic finds the explicit 128-bit counterexample below, with output
inversion at `(64,65)`, 63 input ones, and 16 displaced ones. The script also
extracts disjoint forcing certificates for that pair. Thus the seed-0 `d=14`
construction is rejected; 196 is not a candidate bound. The 64-ID seed-0
success (168 layers) remains only a finite result. Seed 1 also fails at 128
IDs, with an inversion at `(62,63)`, 65 input ones, and 15 displaced ones.
Adding one round per pass (raw coefficient 210) for seed 0 returns `unknown`
after 180 seconds; this is inconclusive. Other seeds, more rounds, or a
different rank-aware schedule remain open. At 64 IDs, tested `d=6` seeds 0--9
and `d=7` seeds 0--14 all fail.

Reproduce the counterexample with:

```sh
python upper-bound/experiments/packets/dyadic_compare_split_sat_screen.py \
  --n 128 --rounds 14 --seed 0 --timeout-ms 180000 --engine sat
```

### Nested matching schedule

The screen now has an experimental `--nested` mode: each local matching is
seeded by `(seed, scale, pass, round, block)`, so the same block matching is
retained when extending the number of rounds or adding larger dyadic scales.
For seed 0, `d=14` sorts at 64 IDs but fails at 128 (inversion `(62,63)`, 65
ones); `d=15` also fails there. `d=16` is `unknown` after 180 seconds, while
`d=17` and `d=20` are SAT-certified sorters at 128 IDs. At 256 IDs, `d=17`
has a concrete counterexample (solver seed 2): output inversion `(126,127)`,
with 129 input ones, 40 displaced ones, and 103 input runs. The `d=18` and
`d=20` checks remain `unknown` at 256 IDs (solver seed 2,
90-second timeout).
Thus the tempting `d=17` scalar candidate is rejected; the schedule is itself an
ordinary scalar comparator network. Uniform `d=18` and `d=20` families would
have depth coefficients 36 and 40, respectively, on power-of-two `n`.
Therefore an all-powers sorting proof for either would imply its respective
limsup coefficient using the existing depth-nonincreasing
`restrictWires` construction for intermediate sizes. This is the main upside
of the candidate, but it is not established. If used inside the UB-25
64-wire packet algorithm instead, each compare-split costs seven layers and
the conditional coefficient is 238. The earlier standard seed-0/1 schedules
are different and retain their failures.

The lift itself is a known sorting-network theorem, not necessarily a new
obstruction: CLRS, 3rd ed., Exercise 28.5-3 states that replacing every
comparator of an `n`-input sorting network by a merge-splitter on sorted
length-`m` lists sorts all `nm` values ([chapter text](https://bobson.ludost.net/books/algo/book6/chap28.htm)).
`PacketGenMerge.genCompareSplit128_outputs_sorted` now kernel-checks the local
64+64 instance: the first and second 64 output ranks are individually sorted,
and every first-half value is at most every second-half value. Together with
the existing seven-layer depth theorem, this packages the exact min/max
packet comparator needed by the dyadic candidate. The global lift from an
arbitrary scalar network is still missing, as is a uniform all-size proof for
the 14-round dyadic schedule.

The exact 14-round prefix screen gives `rho <= 2/25` for fan-ins 1--130.
Together with ten global rounds, it raises the ideal two-scale cross-mode
allowance above `7/20` at conditional coefficient 195. It does not bound the
actual cross-mode operator or close rounding, rare-tail, frontier, or
sorting-sufficiency obligations. The review's go/no-go priority remains the
complete recurrence in a scaled scheduler model.

That simulation is not yet well-defined by the checked transition: the
four/eight-lane physical-state lemmas preserve grouped packet support/order,
but do not assign output packet ranks to next-stage `WireFlow` cuts, while the
global 4096-wire batch gives only logical sorted order on scattered supports.
An arbitrary toy reblocking would test an invented scheduler. First specify
the packet-rank-to-cut map, including partial packets and frontiers. Also,
with 14+10 rounds, the review's suggested `m=16` scale has a crude fresh
positive-spill budget `s/(4m)=3/8` per threshold per stage, versus `3/2048`
at `m=4096`; use the small model for qualitative persistence only.

The rank-target drift has an exact one-round formula for any perfect matching:
`sum_edges |i-j|/(C*(C-1))` on an already rank-sorted array of singleton-key
packets. A random perfect matching has expected drift tending to `1/6`; a
`0.02` one-round budget forces average edge span below `0.04*(C-1)`. See
`rank_target_drift.py` and `MIXING-TAIL.md`. This quantifies the locality cost
of global mixing but does not rule out later rank-aware correction.

For a matching product, the sum of step-profile L1 drift is exactly the total
expected absolute displacement of the induced packet-ID walks. The extended
`global_matching_power_screen.py` estimates this pre-reassembly drift as
`0.333` after nine sampled global rounds for 64--1024 IDs, alongside centered
operator norm estimates `0.156`--`0.205`. Dense step-profile evaluation
matches the path calculation through 256 IDs. This finite sample shows the
rank signal nearly erased by the mixer; it is not a uniform result. A bounded-
depth rank-aware restoration step remains the decisive missing construction.
For the sampled nine-round schedule, the normalized drift stays near `1/3`;
the proposed 78-layer sort acts separately inside each 4096-wire packet and
preserves its threshold count, so it cannot repair this packet-label drift.
That sampled schedule therefore misses the conditional `0.02` error budget
unless a cross-packet correction is added and charged. This is not a
no-go theorem for every matching family.

A stronger exact pre-reassembly gate now uses variance of the centered rank
ramp: any doubly stochastic matching product with centered norm `gamma` has
normalized rank-target drift at least `(1-gamma^2)*(C+1)/(12*(C-1))`, before
rounding. After the nine- or ten-round rounding charge at `m=4096`, the
finite lower bounds at `C=65,536` are about `0.04104` and `0.05647`, both
above the conditional `0.02` tolerance. See the derivation and exact rational
checks in `MIXING-TAIL.md` / `free_matching_bound.py`. This rules out direct
rank-indexed use of the proposed spectral mixer; only a proved rank-aware
target update can evade the gate.

An even stronger estimate allows the best permutation of whole output
packets. Contraction of each rank step by `gamma` forces normalized L1 error
at least `(1-gamma)*(C+1)/(3*C)` after any packet relabeling. After rounding,
the nine- and ten-round gates still force `0.09786` and `0.14722` error at
65,536 packets. Hence whole-packet reassignment is insufficient: comparators
must move values across packet boundaries, or the target state must change in
a way outside this direct rank-indexed model. `RankDriftBound.lean` now
kernel-checks the per-cut inequality: if a fractional output profile has total
mass `h` and centered squared error at most `gamma^2*h*(C-h)/C`, then its L1
distance from every rank step on `h` labels is at least
`2*(1-gamma)*h*(C-h)/C`. Summing the cuts and the rounded numerical gates
remain in `free_matching_bound.py`; the Lean lemma does not prove that the
actual scheduler satisfies its variance premise. Details are in
`MIXING-TAIL.md`.

The exact SAT screen is in `dyadic_compare_split_sat_screen.py` (requires the
Python `z3-solver` package). It finds a 32-wire failure for `(d=5, seed=500001)`;
`(d=6, seed=0)` sorts all Boolean inputs at 32 wires but fails at 64. For 64
wires, all tested seeds 0 through 9 failed at `d=6`, seeds 0 through 14 failed
at `d=7`, and `(d=8, seed=0)` also failed. These are refutations of those
individual schedules, not of the parameter values: each successful choice
must be uniform/provable over all dyadic sizes, and the search has not found
such a choice. For 4096-wire packets, `d≤7` is required for the raw `26d`
coefficient to stay below 200; 64-wire packets raise this screen to `d≤14`.

The two-scale matrix gates also need a dimensionally consistent additive-error
check. The first L1/L2 mixed calculation was retracted. In the corrected
normalized-L2 screen, each compare-split contributes at most `1/(2m)` fresh
error per round. Conservatively charging all 24 rounds to both coarse and
fine components gives conditional stationary error about `0.01578` at zero
cross-mode transfer and `0.03259` at cross norm `0.2` for the 9+15 allocation.
At the determinant contraction threshold `eta=383/1000`, that equilibrium
bound is about `8.14`, so the contraction gate alone is far too weak. The
two-scale model needs `eta<0.0828` even for a `0.02` error target. The actual
projections, cross-map norms, and sorting-sufficient tolerance remain unknown.
See the last section of `MIXING-TAIL.md`.

There is a more basic target-coupling gate: an antipodal matching of 64
already rank-sorted 4096-wire packets creates normalized aggregate profile
error `16/63` in one merge-and-deal. Thus the global spectral contraction of
mean-centered packet counts cannot be read as contraction of sorting error;
the effect on the rank-dependent target must be included. More generally, a
global product with centered norm `45/64` forces asymptotic rank-profile drift
at least `167/12288` before any rank-aware correction, after charging merge
rounding. Subsequent target-aware rebinning may change that drift and must be
proved. The earlier `0.01578` fixed point omits this term and is not an actual
scheduler error bound. See the final section of `MIXING-TAIL.md`.
