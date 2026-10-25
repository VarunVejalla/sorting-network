# Lower-bound survey (2026-10-24)

This survey covers lower bounds on `D(n)`, the minimum depth of a binary-comparator sorting network on `n`
inputs, with `lg = log_2`. It states what the repository proves, the published landscape, the prior repository
attempts to beat `3.2706`, and the directions still open. The directions are the tickets in
[`tickets.json`](tickets.json) (view: [`README.md`](README.md)). Barriers are condensed in
[`ruled-out.md`](ruled-out.md), and the scattered notes are indexed in [`../notes/INDEX.md`](../notes/INDEX.md).

Claim levels follow `AGENTS.md`. **kernel-checked** means a Lean theorem guarded by `#print axioms` (`propext`,
`Classical.choice`, `Quot.sound` only). **published** means a peer-reviewed result that is not formalized here.
**derived** means a repository argument without an audit. **finite/exact** means an exhaustive computation in
Python. **unsure** marks literature details I could not confirm.

## (a) What is proved

All of this lives in `lower-bound/best/`, Lean package `sorting_depth_lower_best`. Build and audit it with
`lake build AKS.Bounds.KahaleAxioms`. The proof map is [`docs/kahale-lower-bound.md`](../../docs/kahale-lower-bound.md).

| Theorem (`lower-bound/best/AKS/Bounds/`) | Statement | Form |
|---|---|---|
| `Kahale.sorting_network_fibonacci_bound` (`AKS/Kahale/NetworkBound`) | `Sorts net → n * fib(net.depth+1) ≤ 2^(net.depth+1) * (net.depth+1)^2` | finite, every `n`, every network |
| `SortingDepth.minimum_fibonacci_bound` (`Kahale.lean`) | `n * fib(D(n)+1) ≤ 2^(D(n)+1) * (D(n)+1)^2` | finite, every `n` |
| `SortingDepth.minimum_exponential_bound` | `n * φ^D(n) ≤ φ * 2^(D(n)+1) * (D(n)+1)^2` (reals) | finite |
| `SortingDepth.minimum_logarithmic_bound` | `0 < n → lg n ≤ (1 - lg φ) D(n) + 2 lg(D(n)+1) + 1 + lg φ` | finite |
| `SortingDepth.eventually_minimum_depth_ge_kahale_logb` (`KahaleAsymptotic.lean`) | `∀ ε > 0, ∀ᶠ n, (c - ε) lg n ≤ D(n)` | eventual |
| `SortingDepth.liminf_minimum_div_logb_ge_kahale` | `c ≤ liminf (D(n) / lg n)` in `ℝ` | liminf |

Here `c = Kahale.depthConstant = 1/(1 - lg φ) ≈ 3.270559454`.

**Model.** `D(n) = SortingDepth.minimum n` is defined in the legacy package
(`upper-bound/alternatives/legacy/AKS/Bounds/Upper.lean`, `Nat.find` over `ComparatorNetwork n` with
`Sorts.{0}` and `depth`). Comparators are standard, min to the lower index. The depth is the greedy layering of the
comparator list, as in `TimedExecution` and `GreedyLayers`.

**Proof shape.** The argument is a reconstruction of KLMPSS §5, not a copy. A suffix of `s` stages has a rank cover
of size `2^s` (`Fanout`). Zero-certificate heights move by a factor of at most 2 per stage (`BinomialPotential`,
`LayerPotential`). Approximate selection then forces `n·C(d-s, s) ≤ 2^(d+1)(s+1)` (`SelectionCounting`,
`LayeredBound`). Summing over `s` gives `fib(d+1)` (`FibonacciBound`). The paper's weighted optimization is
replaced by this single-term-per-`s` sum, which loses only a polynomial factor.

**Dependencies.**
- The finite inequalities depend only on the comparator model and the Kahale modules.
- The `ℝ`-valued `liminf` needs `IsCoboundedUnder (· ≥ ·)`, an eventual upper bound on `D(n)/lg n`.
  `minimum_div_logb_cobounded` gets it from the legacy `minimum_depth_le : D(n) ≤ 102·10^62·⌈lg n⌉`
  (Seiferas/Paterson for `n ≥ 1024`, bitonic below that). It does not use the 789.75 package.
- `eventually_minimum_depth_ge_kahale_logb` does not need the cobounded premise. It still imports the legacy package
  through the definition of `minimum`.
- LB-11 (`AKS/Bounds/KahaleUnconditional`) adds an `EReal` `liminf`, an every-`c < 1/(1-lg φ)` eventual form and an
  explicit-premise real `liminf`, none using `minimum_depth_le`.

**Strength at finite `n` (computed here, model).** The finite Fibonacci inequality is weak for moderate `n`. The
table gives the smallest `d` it allows, next to the elementary counting bound `⌈lg(n!)/⌊n/2⌋⌉`:

| `n` | Kahale finite | counting `lg n!/(n/2)` | fan-in `lg n` |
|---|---:|---:|---:|
| `2^16` | 20 | 30 | 16 |
| `2^32` | 61 | 62 | 32 |
| `2^36` | 73 | 70 | 36 |
| `2^64` | 157 | 126 | 64 |

Kahale overtakes the counting bound only near `n ≈ 2^33`. Both are now formalized (LB-01,
`AKS/Bounds/FiniteLower`: `minimum_ge_max_bounds`, `minimum_two_pow_sixteen_ge`). `ComparisonTrace.exec_trace_injective` in `lower-bound/experiments` (output plus swap
trace determines the input) is most of the counting bound.

**Experiments package** (`lower-bound/experiments/AKS/Kahale/*`, about 50 modules, each with an `*Axioms` guard).
These are kernel-checked lemmas, identities and finite counterexamples behind the routes in (c). None of them
improves the coefficient. The most reusable ones:
- `CertificateCompatibility`: in a sorting network, a zero certificate on a later output meets a one certificate on
  an earlier output.
- `UnionCoupling`: at an active comparator, `z_max + o_min ≤ n+2`.
- `RankCongestion`: coalition Hall capacity at a suffix cut.
- `ComparisonTrace`: trace injectivity.
- `ComparatorInformation`, `RankFiberMerge`: exact single-gate information.
- `CoupledFaces`, `FaceTransport`, `FaceSortingCriterion`: two-bit face coalescence.
- `MethodBarrier`, `PositionalBarrier`: arithmetic witnesses for the relaxation barrier.

## (b) Literature landscape

### Sorting-network depth

- **Fan-in (folklore, certain).** `D(n) ≥ ⌈lg n⌉`.
- **Counting (folklore, certain).** A network with `G` comparators distinguishes at most `2^G` input orders, so
  `G ≥ lg n!` and `D(n) ≥ lg(n!)/⌊n/2⌋ = 2 lg n - O(1)`. Recent papers call this the folklore `(2 - o(1)) lg n`.
- **Yao, "Bounds on selection networks", SIAM J. Comput. 1980 (confident).** Depth about `(2.41 - o(1)) lg n`.
  KLMPSS cite it as the previous best for sorting. I am **unsure** whether `2.41 = 1+√2` exactly, and whether Yao
  states the bound for sorting or for selection networks.
- **Kahale, Leighton, Ma, Plaxton, Suel, Szemerédi, "Lower bounds for sorting networks", STOC 1995 (confident).**
  - Depth `(c - o(1)) lg n` with `c ≈ 3.27`.
  - Size `(1.12 - o(1)) n lg n`, the first improvement over the information bound by more than a lower-order term.
  - The size bound extends to networks that sort a fixed fraction of input permutations.
  - Sources: [author copy](https://research.engineering.nyu.edu/~suel/papers/size.pdf) and the local scan
    `docs/225058.225178.pdf`. `docs/kahale-lower-bound.md` gives the title as *Improved lower bounds…*; the
    title should be checked.
- **Nothing better is known as of 2023 (confident).** Two papers still call `3.27 lg n` the record:
  Dobrokhotova-Maikova, Kozachinskiy and Podolskii, *Constant-depth sorting networks*
  ([ITCS 2023](https://drops.dagstuhl.de/storage/00lipics/lipics-vol251-itcs2023/LIPIcs.ITCS.2023.43/LIPIcs.ITCS.2023.43.pdf),
  [arXiv 2208.08394](https://arxiv.org/abs/2208.08394)), and Kozachinskiy and Podolskii (?), *Towards simpler
  sorting networks and monotone circuits for majority*
  ([arXiv 2310.12270](https://arxiv.org/abs/2310.12270)). I found no later improvement in a quick search.
  This is **not exhaustive** for 2024–2026.

### Size, merging and selection

- **Size (confident).**
  - Van Voorhis (1972): `S(n) ≥ S(n-1) + ⌈lg n⌉`, giving `n lg n - O(n)`.
  - KLMPSS: `1.12 n lg n`.
  - Upper bounds are `O(n log n)` via AKS. The best constant is not tracked here.
- **Merging (confident on the shape, unsure on exact constants).**
  - Merging two sorted lists of length `n` needs depth `⌈lg 2n⌉` by fan-in, and Batcher's merger meets it. Depth is
    therefore settled.
  - Size: Yao and Yao (JACM 1976) gave lower bounds.
  - Miltersen, Paterson and Tarui, *The asymptotic complexity of merging networks* (JACM 1996): Batcher's
    `(1/2) n lg n` is optimal up to lower-order terms.
  - Kernel-checking these would be a self-contained published result (LB-12).
- **Selection.**
  - Alekseev (1969): size `≥ (n-t)⌈lg(t+1)⌉` for `(n,t)`-selectors (fairly confident).
  - Yao (1980), depth bounds for selection.
  - Pippenger, *Selection networks* (SIAM J. Comput. 1991): size bounds near `2 n lg n` for medians (bounds
    **unsure**).
  - Jimbo and Maruoka: improved size constructions.
  - Depth lower bounds for selectors with constants close to sorting's: **unsure**.

### Approximate and average-case sorting

- **ε-halvers (AKS, confident).** Expander halvers achieve depth `O(log(1/ε))`; see the repo's Paterson modules.
  Tight lower bounds on halver depth as a function of `ε`: **unsure**. LB-05 derives one from the Kahale machinery.
- **Leighton–Plaxton (FOCS 1990, fairly confident).** *A (fairly) simple circuit that (usually) sorts* has depth
  `≈ 7.44 lg n` and sorts all but a superpolynomially small fraction of permutations.
- **Hypercubic sorting networks** (Leighton–Plaxton, SIAM J. Comput. 1998): depth `2^{O(√(lg lg n))} lg n`.
- KLMPSS's size bound covers fraction-sorting. Whether their **depth** bound extends to it is **unsure** (LB-10).

### Restricted network classes (superlogarithmic lower bounds exist)

- **Shuffle-based networks (confident).** Plaxton and Suel prove depth `Ω(lg² n / lg lg n)`
  ([hylow](https://research.engineering.nyu.edu/~suel/papers/hylow.pdf)), so shuffle-unshuffle structure cannot
  reach `O(log n)`.
- **Shellsort networks (fairly confident).** Cypher (SIAM J. Comput. 1993) proves size `Ω(n lg² n / lg lg n)`.
  Plaxton, Poonen and Suel (FOCS 1992) and Plaxton and Suel (J. Algorithms 1997) improve the Shellsort bounds.
- **Periodic networks.**
  - Dowd, Perl, Rudolph and Saks: the periodic balanced network, `lg² n`.
  - Kutyłowski, Loryś, Oesterdiekhoff and Wanka: faster periodic constructions.
  - Lower bounds for constant-period networks: **unsure**.
- **Networks of k-sorters (confirmed via the arXiv HTML).** Dobrokhotova-Maikova, Kozachinskiy and Podolskii
  (ITCS 2023):
  - For `d = 1, 2`, `k = n`.
  - For `d = 3`, `k = ⌈n/2⌉`, tight.
  - For `d = 4`, `k = Θ(n^{2/3})`.
  - In general `k = Ω(n^{1/⌈d/2⌉})`, i.e. `d ≥ 2 log_k n - O(1)`, twice the trivial bound.
  - The 2023 follow-up applies this to monotone majority circuits.
  - This is the natural lower-bound side of UB-08.
- **AKS-type, separator-based networks.** I know of no published lower bound on their constants. The repo's upper
  cost models are design lower bounds, not theorems about every network.

### Other models (context only)

- **Parallel comparison model** (Valiant 1975; Häggkvist–Hell; Alon–Azar, SIAM J. Comput. 1988). With `n`
  processors, sorting needs `Ω(log n)` rounds. This model is adaptive and strictly stronger than networks, so it
  gives no better constants for networks. Constants: **unsure**.
- **Oblivious RAM sorting** (Lin, Shi and Xie, [2018/227](https://eprint.iacr.org/2018/227.pdf)): `n log n`
  barriers for oblivious algorithms. This is a different cost measure.
- **Boolean and monotone circuits.** Sorting networks are monotone circuits of the same depth, but monotone-depth
  lower bounds for sorting or majority are only `Ω(log n)` with weak constants.
- **Adversary arguments.** Kahale et al. use certificate heights plus suffix fan-out. Yao's argument uses a
  2-adversary on selection. A two-sided (0/1) adversary is the structure that LB-02 tries to exploit.

### Exact small n

Source: the [Dobbelaere table](https://bertdobbelaere.github.io/sorting_networks.html) (confident).

| `n` | 2 | 3–4 | 5–6 | 7–8 | 9–10 | 11–12 | 13–16 | 17 | 18–20 | 21–24 | 25–28 | 29–32 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `D(n)` | 1 | 3 | 5 | 6 | 7 | 8 | 9 | 10 | 10–11 | 10–12 | 10–13 | 10–14 |

Who proved which values:
- `n ≤ 8`: classical.
- `n = 9, 10`: Parberry 1991.
- `n ≤ 16`: Bundala and Závodný, SAT, 2014.
- `n = 17`: Codish, Cruz-Filipe, Ehlers, Müller and Schneider-Kamp, *Sorting networks: to the end and back
  again*, JCSS 2016/19, via Ehlers–Müller SAT.
- `D(18..32) ≥ 10` follows only from monotonicity and `n = 17`, so the finite lower bounds are stuck.
- Size optimality: `n = 9` (Codish et al., 25 comparators), `n = 11, 12` (Harder).
- Cruz-Filipe, Larsen and Schneider-Kamp formally verified size-optimality certificates in Coq/Isabelle
  (fairly confident).

### Gap to the upper bounds

- Published limsup constants: Paterson about 6100, then Seiferas, then Chvátal's DCS-TR-294 about 1830.
- The repo has a kernel-checked 789.75 (`upper-bound/STATUS.json`).
- The lower bound is 3.27, a factor of about 240.
- No result I know closes any constant fraction of the gap from below since 1995. Most of the gap is believed to
  sit on the upper side; this is an opinion, not a theorem.

## (c) Prior repository attempts

Every route below keeps the kernel-checked coefficient at `3.2706`. The chain runs roughly in date order,
2026-09 to 2026-10-12. Notes are in `docs/`, scripts in `lower-bound/experiments/scripts/`, and the ticket in
brackets is the matching LB ticket.

1. **Scalar binomial system** (`kahale-method-barrier.md`, `MethodBarrier.lean`) [LB-20, rejected].
   - A fractional height population saturates every prefix counting inequality at once at rate `3.2706`, including
     the full weighted binomial sums.
   - Integral histogram rounding preserves this.
   - **Barrier:** recombining or restoring discarded terms of the Kahale inequalities cannot raise the coefficient.
2. **Positional constraints** (`kahale-positional-barrier.md`, `PositionalBarrier.lean`) [LB-21, rejected].
   - An explicit schedule on `N_d = ⌊2^d/((d+1)F_{d+1})⌋` wires meets `h_{d-s}(i) ≥ s+1` for all `i ≥ 2^{s+1}`.
   - **Barrier:** the zero-height boundary positions are satisfiable at the Kahale rate. The schedule does not sort.
3. **Certificate families and union coupling** (`kahale-certificate-families.md`, `kahale-union-coupling.md`,
   `CertificateCompatibility.lean`, `UnionCoupling.lean`) [LB-22, parked, feeds LB-02].
   - The 161-wire barrier schedule fails sorting because a zero certificate (77 inputs, needs 87) and a one
     certificate (65, needs 76) are disjoint.
   - Kernel-checked: certificate intersection characterizes sorting, and `z_max + o_min ≤ n+2`.
   - **Barrier:** these are local or terminal constraints. No depth-rate inequality has been derived from them.
4. **Joint monomial potentials** (`kahale-joint-potential.md`, `JointPotential.lean`) [LB-23, rejected].
   - `Σ z_i^p o_i^q` with a uniform per-stage factor gives coefficient at most `2`.
   - `(z, o)` does not determine its own update; this is kernel-checked on 4 wires.
   - **Barrier:** time-independent additive monomial potentials are dead.
5. **Pairwise union costs and suffix potentials** (`kahale-weighted-union.md`, `kahale-suffix-potential.md`,
   `PairUnionRecurrence.lean`, `kahale-pair-union-rate.md`) [LB-24, rejected].
   - Pair costs `Z_ij`, `O_ij` give a closed upper recurrence.
   - On 5 wires, pair costs restore the remaining-depth information that per-wire costs lose.
   - The rate test fails to separate. The barrier schedule plus 2 layers meets the full pair relaxation at `N_d`
     (`d <= 64`).
   - **Barrier:** the defect is on middle wires, where union bounds are capped at `n`. The pair condition is
     per-wire at the end.
6. **Rank congestion and coalition Hall** (`kahale-rank-congestion.md`, `kahale-congestion-rate.md`,
   `RankCongestion.lean`, `CongestionBarrier.lean`) [LB-25, parked].
   - A coalition of 12 zeros has only 11 targets in the barrier schedule.
   - Under full reachability every coalition inequality is automatic (kernel-checked).
   - **Barrier:** obstructions sit in terminal layers. A rate needs a factor `r > 1` accumulated over `θd` stages
     (`δ = θ lg r`), and the symbolic searches were inconclusive.
7. **Information accounting, slot-saving banks** (`kahale-proof-plan.md`, `kahale-target-four.md`,
   `kahale-swap-charging.md`, `kahale-layer-bank.md`, `kahale-boundary-transfer.md`, `kahale-transfer-charging.md`,
   `kahale-rankset-transition.md`, and about 15 modules: `ComparisonTrace`, `ComparatorInformation`,
   `BoundaryTransfer`, `RankSetTransition`, `HistoryInnovation`, …) [LB-26, parked].
   - Exact identity: `M - lg n! = (M - G) + Σ_g (1 - h_g)`.
   - A slot-saving fraction `ρ` gives coefficient `2/(1-ρ)`. Kahale corresponds to `ρ ≈ 0.388`; `ρ = 1/2` gives 4.
   - **Barrier:** no charging lemma for gate excess. Parallel layers can gain more than the sum of their single-gate
     gains (sorted blocks), and endpoint-controlled banks give no local inequality.
8. **Hierarchy of cuts** (`kahale-hierarchy-layer.md`, `HierarchyRefinement.lean`) [part of LB-26].
   - Joint observation of nested scales adds no Shannon entropy (kernel-checked).
   - **Barrier:** a gain would need weighted or nonlinear inter-scale inequalities.
9. **Occupation spectra and degree recycling** (`kahale-layer-occupation.md`, `kahale-degree-recycling.md`,
   `OccupationLayer.lean`, `OccupationCounterexample.lean`) [LB-27, rejected].
   - Johnson-graph coalescence budget.
   - **Barrier:** the local charge from occupation reserve to certificate inefficiency is false at arbitrarily large
     sizes. One comparison of sorted-block medians clears all spectral degrees. Equal-height comparators can finish
     sorting (4 wires).
10. **Activation hypergraphs and preparation charges** (`kahale-joint-groups.md`, `kahale-activation-scales.md`,
    `kahale-certificate-preparation.md`) [LB-28, rejected as stated].
    - Conditional certificate size is at least pivotal group plus meet-graph cover.
    - **Barrier:** the full certificate potential has amortized growth `3/2` per layer on depth-log aligned prefixes
      (`(7/192)(3/2)^d ≤ K_d/2^{d-1}`). A uniform amortized growth bound below `3/2` is false, so charging raw growth
      cannot work.
11. **Residual image difficulty** (`kahale-image-difficulty.md`) [LB-29, rejected for dependency-only charges].
    - Exact completion depths of every image through 5 wires.
    - **Barrier:** dependency or reachability models have a ceiling of one `lg` coefficient on powers of two. Cube
      costs and information costs do not add.
12. **Shared polarity and witness charges** (`kahale-joint-polarity.md`, `kahale-witness-charge.md`)
    [LB-30, parked, continued in LB-08].
    - Additive mixed-witness charges of every order, even signed ones, fail by an exact LP dual.
    - Signed **quadratic** cross-image charges recover `D(4) = 3` and `D(5) = 5`.
    - **Barrier:** no scale-compatible nonlinear charge is known.
13. **Fiber-charge correction chain** (`kahale-preimage-capacity.md`, `kahale-capacity-lift.md`,
    `kahale-singleton-correction.md`, `kahale-pair-correction.md`, `kahale-pair-constraint-generation.md`,
    `kahale-low-rank-barrier.md`) [LB-31, rejected].
    - The 10-term 4-wire charge fails on 5-wire fibers, and singleton corrections cannot repair it.
    - Quadratic pair corrections fit 4 and 5 wires but are infeasible on 6 wires (exact Farkas certificate, 2102
      transitions).
    - **Barrier:** a standalone potential reading only global input weights `≤ 3` with unit layer drop changes by
      at most `3⌈lg n⌉`. Its coefficient is at most 3, below Kahale.
14. **Coupled Boolean faces and discrepancy transport** (`kahale-coupled-faces.md`, `kahale-face-transport.md`,
    `CoupledFaces.lean`, `FaceTransport.lean`, `FaceSortingCriterion.lean`) [LB-32, parked].
    - Exact 4-execution model; coalescing every 2-bit face suffices for sorting (kernel-checked).
    - **Barrier:** pair-matrix closure is open for ordered comparators. A counterexample exists for unrestricted
      orientation, and no depth-rate lemma is known.

**Synthesis.**
- Routes 1–2 show that **every scalar or positional relaxation of Kahale's argument is tight at 3.2706**. Any gain
  must use joint structure that sorting forces: zero/one certificate interplay, multiple thresholds, or shared
  inputs.
- Routes 4, 10, 11 and 13 show that **simple additive potentials over that joint structure are capped at or below
  Kahale**: 2, raw growth `3/2`, `1·lg`, and 3.
- The live leads are nonlinear (route 12), information/slot (route 7), and two-sided certificate (route 3). Each has
  a precise missing lemma.

## (d) Ranked directions (not ruled out)

Ranking weighs the probability of a useful outcome against cost. Items 1, 4, 5 and 6 are partial results with high
success probability. Items 2, 3 and 8 are the attempts on the constant itself.

1. **LB-01 — Explicit finite lower bound: max(fan-in, counting, Kahale).**
   - *Why:* below `n ≈ 2^33` the formalized bound is weaker than folklore (table in (a)). A combined finite theorem
     is the honest best statement for every `n`.
   - *First test:* Lean `Sorts net → n.factorial ≤ 2^(comparator count)` from `exec_trace_injective`, then
     `lg n! ≤ D(n)·⌊n/2⌋`.
   - *Risk:* none mathematical. The constant is unchanged.
2. **LB-02 — Two-sided certificate-height relaxation.**
   - *Why:* the scalar method tracks only zero heights. The 161-wire extremal schedule fails exactly because its zero
     and one certificates are disjoint (route 3). Imposing both heights plus the kernel-checked intersection or
     `n+2` coupling is the smallest relaxation that sees that defect.
   - *First test:* an exact DP/LP for the joint `(h_0, h_1)` histogram relaxation, analogous to
     `kahale_height_barrier.py`. Is the optimal rate above `3.2706`? Then try the mirrored positional schedule as a
     witness.
   - *Risk:* a mirrored (min/max symmetric) schedule may satisfy both sides at the same rate, and the coupling is
     local. Quick to kill.
   - *Outcome (2026-10-24): killed.* The joint relaxation, with graded requirements and active width, has rate
     exactly 3.2706. A positional schedule meets both sides (`docs/kahale-two-sided-heights.md`). Next: cross-wire
     (LB-24).
   - *Follow-up LB-24 (2026-10-24): killed.* Pair union costs also have rate 3.2706 (`docs/kahale-pair-union-rate.md`).
     The defect sits on middle wires, where every union bound saturates at `n`. Next: mixed-polarity restriction
     families, or correlation (BK/Reimer) potentials.
   - *Follow-up LB-33 (2026-10-24): killed.* Harris potentials equal the sizes relaxation (monomials `p^c`), and BK is
     vacuous on middle wires: the overlap-only share is about 1, and the sorted target has no disjoint mass
     (`docs/kahale-correlation-potential.md`). The barrier defect is a read-once amplification deficit
     (`c ≈ 0.25` bits/stage), which no sound bound yet sees. Next: hybrid-schedule kill test, then LB-34.
3. **LB-03 — Coupled information and certificate tradeoff.**
   - *Why:* the counting bound (2) and Kahale (3.27) are separately tight. Kahale-extremal schedules may waste many
     comparisons (low `h_g`). A coupled inequality "height slack + information slack ≥ ..." could beat both, whereas
     route 7 needed a universal saving.
   - *First test:* exact or analytic information gain `Σ(1-h_g)` of the positional barrier family (route 2) and of
     sorted-block families, as a function of `d`. If extremal schedules have `ρ` well above 0.388, formulate the
     tradeoff.
   - *Risk:* sorting networks near the bound could be information-efficient. The same charging difficulty as route
     7 may return.
4. **LB-04 — k-sorter networks (Dobrokhotova-Maikova, Kozachinskiy, Podolskii 2023).**
   - *Why:* a published bound for a restricted class, `d ≥ 2 log_k n - O(1)`, tight at `d = 3`, with `Θ(n^{2/3})`
     at `d = 4`. It is directly relevant to UB-08 (compiling high-arity sorters).
   - *First test:* Lean model of k-sorter layers and the `d = 3`, `k ≥ ⌈n/2⌉` lower bound.
   - *Risk:* a new network model is needed; the general-`d` proof may be long.
5. **LB-05 — Depth lower bound for ε-halvers and approximate selectors.**
   - *Why:* `ApproxSelection` and `SelectionCounting` already handle approximate selection. A standalone theorem
     "an ε-halver needs depth ≥ f(ε, n)" calibrates the upper-side separator/halver tickets (UB-04, UB-06,
     ruled-out "expander ε-halvers").
   - *First test:* state the strongest bound the existing modules give for an `(n, ε)`-halver and prove it by reuse.
   - *Risk:* the bound may be the trivial `lg(1/ε)`-type, with no news.
6. **LB-06 — Kernel-checked exact `D(n)` for small `n`.**
   - *Why:* finite values are the only lower bounds that are exactly known. The repo has none formal. Without
     `native_decide`, `n ≤ 8` (perhaps 10, via Parberry's first-layer normalization and 0-1 principle pruning) is a
     realistic target.
   - *First test:* `D(4) = 3`, `D(5) = 5` by kernel `decide` over normalized prefixes.
   - *Risk:* kernel evaluation cost grows explosively. No asymptotic consequence.
7. **LB-07 — Formalize the KLMPSS size bound `(1.12 - o(1)) n lg n`.**
   - *Why:* a published, unformalized result of the same paper. It probably reuses certificate machinery.
   - *First test:* map the paper's §3–4 onto existing modules and list the missing lemmas.
   - *Risk:* a long proof with its own optimization; the depth coefficient is unchanged.
8. **LB-08 — Scale-compatible nonlinear witness charge at varying baselines.**
   - *Why:* signed quadratic cross-image charges are the only route that reproduced exact small depths (route 12).
     The low-rank barrier recommends conditional pair routing at central Hamming weights.
   - *First test:* exact 6–7-wire screens of pair routing at central baselines. Does a quadratic charge with unit
     layer drop and sorted endpoint survive (LP feasibility, Farkas certificate otherwise)?
   - *Risk:* finite fits keep failing at the next width (route 13 pattern).
9. **LB-09 — Shuffle-based networks: Plaxton–Suel `Ω(lg² n/lg lg n)`.**
   - *Why:* a superlogarithmic published bound for a restricted class.
   - *First test:* precise model statement and a proof outline.
   - *Risk:* a long proof. The class is far from the repo's upper architecture.
10. **LB-10 — Depth for "usually sorts" networks.**
    - *Why:* the Leighton–Plaxton 7.44 upper bound makes this the model with the smallest gap. Does the Kahale depth
      argument survive restriction to a `1 - o(1)` fraction?
    - *First test:* check where `SelectionCounting` uses all inputs (worst case versus averaged certificates).
    - *Risk:* the certificate argument is inherently worst-case.
11. **LB-11 — Headline hygiene.**
    - *Why:* state a liminf form (`EReal`/`ENNReal`-valued, or the eventual form) that does not need the legacy
      `102·10^62` upper bound. Alternatively move `minimum` to a small neutral module so the lower package does not
      depend on the legacy upper package.
    - *First test:* an `EReal` liminf theorem without the cobounded premise.
    - *Risk:* low. The value is clarity of trust, not mathematics.
12. **LB-12 — Merging networks.**
    - *Why:* the depth lower bound `⌈lg(m+n)⌉` (fan-in) is easy, and Miltersen–Paterson–Tarui size optimality is a
      published bound.
    - *First test:* the depth bound in Lean, reusing the fan-in lemma from LB-01.
    - *Risk:* low value for the main question.

**Main risk across the board.** The repo's history shows that every finite fit failed at the next width, and every
additive potential was capped. A new constant needs a genuinely new compatibility inequality whose loss is
exponential (a fixed `δ > 0` in `n·F_{d+1} ≤ 2^{(1-δ)d}·poly(d)`), not polynomial. Stop a candidate as soon as its
exceptions can be `Θ(n log n)` (`docs/kahale-proof-plan.md`, step 4).
