# Lower-bound ideas ruled out (with reasons)

Keep this list so nobody repeats these ideas. Each entry states exactly what is dead. Most barriers apply to a
specific family, not to the general idea behind it; recheck an entry if its assumptions change. Details are in
`docs/` (see [`../notes/INDEX.md`](../notes/INDEX.md)).

**A sufficient form for any gain.** An improvement needs an exponential loss, i.e. a fixed `δ > 0` with
`n·F_{d+1} ≤ 2^{(1-δ)d}·poly(d)`. Coefficient 3.3 needs `δ ≈ 0.0027`; 4 needs `δ ≈ 0.056`. A polynomial or
`O(log)`-layer terminal loss changes nothing (`docs/kahale-congestion-rate.md`).

* **Recombining Kahale's binomial inequalities (LB-20).**
  - A fractional height population saturates every prefix counting constraint at once at `3.2706`, including the
    full weighted sums.
  - Integral rounding keeps this.
  - Evidence: `kahale-method-barrier.md`, `MethodBarrier.lean` (kernel-checked witness arithmetic).
* **Zero-height positional constraints (LB-21).**
  - An explicit schedule on `⌊2^d/((d+1)F_{d+1})⌋` wires meets `h_{d-s}(i) ≥ s+1` for all `i ≥ 2^{s+1}`. It does
    not sort.
  - Evidence: `kahale-positional-barrier.md`.
* **Two-sided per-wire certificate heights (LB-02).**
  - The joint `(z, o)` relaxation has rate exactly `3.2706`. It includes zero and one heights, the graded window
    requirements on both sides, the `n+2` coupling and the active width `j-i <= 2^(s'+1)-1`.
  - The histogram form projects onto Kahale's system. Kahale's block-halving schedule, with over-wide blocks idled,
    meets every positional constraint at `N_d` wires (exact check, `d <= 1024`).
  - **Barrier:** per-wire two-sided data is exactly the attainable rank interval. The zero and one requirements bind
    on disjoint wires (top and bottom `2^(s+1)` positions), so no per-wire coupling binds. Any gain must be
    cross-wire (disjoint `S in Z_j`, `T in O_i`; LB-24).
  - Evidence: `kahale-two-sided-heights.md`, `kahale_two_sided_heights.py`.
* **Pairwise union-cost matrices `Z_ij`, `O_ij` with the closed layer recurrence (LB-24).**
  - The terminal pair condition (no disjoint zero certificate of `j` and one certificate of `i`, `i < j`) is
    equivalent to the per-wire thresholds. Pairs can only sharpen upper bounds via overlap, and the relaxation sits
    inside Kahale's (`n*_pair <= U_d`).
  - The LB-02 barrier schedule plus 2 odd-even layers meets the full `n x n` pair relaxation at `N_d` (exact,
    `d = 24..64`, `n <= 16530`). Within the schedule family the pair matrix costs about 1 bit of `n`, constant in `d`.
  - **Barrier:** the actual defect is on middle wires (rank error about `0.07 n`), where every union bound is capped
    at `n`. `Z` and `O` never interact, and overlap savings die out before the binding window. Any gain needs
    non-saturating, mixed-polarity, three-or-more-way overlap information.
  - Evidence: `kahale-pair-union-rate.md`, `kahale_pair_union_rate.py`.
* **Correlation (Harris/FKG, BK/Reimer) probability potentials (LB-33).**
  - Harris lower bounds stay monomials `p^c`, where `c` is the min-plus sizes bound. Since `p^m <= P(Bin(n,p) >= m)`,
    the pointwise-in-`p` window requirement fails iff the sizes requirement fails. Per-wire, pair and k-wise Harris
    potentials have exactly the sizes rate `3.2706` (proof in the note).
  - BK only bounds `mu(A n B) <= mu(A)mu(B) + overlap-only mass`. On middle comparators the overlap-only share reaches
    `>= 0.96` within about `log2 n + 7` stages (exact, `n <= 14`), and the sorted target has zero disjoint mass on
    middle pairs. Correlation is required by sorting, so it cannot be charged. Mixed-polarity events get no lower
    bounds from FKG or Reimer.
  - The barrier's middle-wire sharpness deficit (`c ≈ 0.25` bits of `n` per stage) was a separate lead; see LB-35 below.
  - Evidence: `kahale-correlation-potential.md`, `kahale_correlation_potential.py`.
* **Middle-wire sharpness and influence potentials (LB-35).**
  - Proved: influence is conserved at a comparator, and the sound growth bound (factor 2 per layer) propagates to the
    formula leaf count, so a sum-rule potential never binds.
  - Numeric only: a hybrid with no extra depth (barrier, then mean-rank pairing in the last `K` stages) repairs the
    defect on the actual network. Sharp-and-placed wires go from 2.2% to 99.4% at `d = 80`, `n = N_d`. Heights and wire
    relaxations pass through `d = 80`, the pair relaxation through `d = 56`. Sharpness survives to `64 N_d`, past where
    the relaxations fail.
  - **Not a proved rate barrier.** The heuristic's trend extrapolates to about 4.3, an upper estimate only.
  - Sharpness was not the whole defect: exact sorting of random inputs still lags `N_d` by about 0.21 bits per stage,
    and structured inputs stay wrong by about `0.04 n`. Those two are not ruled out.
  - The conditional bound `(a + 1/(2 lg kappa)) lg n` exceeds 3.5 only with `a = 2`, `kappa <= 1.26` and no comparator
    sharing. Sound values are `a = 1`, `kappa = 2`. Formula-only 3.5 needs `n^3.5` against a known `n^2`.
  - Evidence: `kahale-amplification-kill.md`, `kahale_amplification_kill.py`.
* **Mixed-polarity restriction families (LB-34).**
  - Proved: a `(1,0)`-forcing pair `(S, T)` projects to a zero certificate `S`, and any zero certificate with `|S| <= j`
    gives the pair `(S, complement of S)`. So mixed polarity adds no witness, and compatibility only deletes candidates.
  - Numeric: the pair family with supports finds no inversion on `tr` or the barrier at `d = 40, 44`, `B <= 4`, though
    inversions exist. Size-ranked one-polarity beams are blind too (`B = 64`, `d = 48`).
  - `tr` itself breaks: worst rank error found is `0.29 n` at `d = 64`, from a single stray (1 to 10 wrong wires). The
    stray is a shared Fibonacci proof tree at the barrier/tail boundary, then an AND-free path. Inputs show no structure.
  - **Not ruled out:** the one-polarity tree family (OR by uncapped LB-24 cost, AND by set union) fails on `tr`, the barrier
    and random wiring at `N_d`, `d >= 40`. That is a sound test of one network, not a bound. Sorters pass, and Batcher
    reaches `N_d` through `d = 44`. Its schedule optimum cannot be evaluated, so it gives no coefficient.
  - Evidence: `kahale-worst-case-inputs.md`, `kahale_worst_case_inputs.py`.
* **Information/certificate tradeoff on extremal schedules (LB-03).**
  - Proved: every sorter has total waste exactly `M - lg n!`, a function of `(n, d)`. Height slack and information slack
    are functions of `(n, d)` too, so a coupling of those totals is a depth statement with no independent variable.
  - Proved: the marginal form of "certificate efficiency forces waste" is false. Doubling networks have equal heights at
    every gate and exactly zero marginal waste for `lg n` layers, so a charge needs a bank of size `Θ(n lg n)` mid-run.
  - Proved: with the true `h_g`, the candidate at coefficient `c` is the LB-26 charging lemma with threshold `2/c`.
  - Numeric: at `d = 64`, `n = 16530` the barrier and `tr` both pass heights and wire, yet `Σ H(S_g)/lg n!` is 0.913 and
    1.83. Efficiency does not determine waste. The ticket's test `ρ > 0.388` is vacuous at `N_d`: every sorter has 0.62 to 0.72.
  - **Not ruled out:** a bank with uncontrolled interior range (that is LB-26). Whether the best schedule's excess stays
    below `0.02 nd`: `tr` reaches 0.38 of it at `d = 64`, and growing.
  - Evidence: `kahale-information-screen.md`, `kahale_information_screen.py`.
* **Additive monomial joint potentials `Σ z_i^p o_i^q` with a uniform per-stage factor (LB-23).**
  - The coefficient is at most `2`.
  - `(z, o)` does not determine its own update, even at non-redundant comparators (kernel-checked on 4 wires).
  - Evidence: `kahale-joint-potential.md`.
* **Local occupation/spectral charge for certificate inefficiency (LB-27).**
  - False at arbitrarily large sizes: one comparison of sorted-block medians clears every non-constant spectral
    component.
  - Equal-height comparators can finish sorting, so no positive local height-loss charge exists
    (`OccupationCounterexample.lean`).
  - Evidence: `kahale-layer-occupation.md`, `kahale-degree-recycling.md`.
* **A uniform amortized growth bound on the full certificate potential (LB-28).**
  - Depth-log aligned prefixes have amortized growth exactly `3/2` per layer.
  - Paying for preparation by averaging raw growth fails. A charge must measure the residual sorting work.
  - Evidence: `kahale-certificate-preparation.md`.
* **Dependency / reachability-only charges on residual images (LB-29).**
  - Asymptotic ceiling of one `lg` coefficient on powers of two.
  - Cube costs and information costs cannot simply be added.
  - Disjoint copies of a finite obstruction run in parallel.
  - Evidence: `kahale-image-difficulty.md`.
* **Additive mixed-witness charges of any order, even signed (part of LB-30).**
  - An exact LP dual (a two-line 4-wire proof) refutes them.
  - Only signed **quadratic** cross-image charges escape; see LB-08 below.
  - Evidence: `kahale-witness-charge.md`.
* **Fiber-charge corrections (LB-31).**
  - The 10-term 4-wire charge breaks on actual 5-wire conditional fibers (drop 2), and singleton-routing
    corrections cannot repair it (drop 5/3 with identical singleton routing).
  - The quadratic pair-mass correction that fits 4 and 5 wires is infeasible on 6 wires (exact Farkas certificate,
    2102 transitions).
  - **Structural barrier:** any standalone potential reading only global input weights `≤ 3`, with unit layer drop
    and the sorted endpoint value, has total range `≤ 3⌈lg n⌉`, so its coefficient is at most 3.
  - Evidence: `kahale-capacity-lift.md`, `kahale-singleton-correction.md`, `kahale-pair-constraint-generation.md`,
    `kahale-low-rank-barrier.md`.
* **Central-band signed quadratic witness charges (part of LB-08).**
  - Rank-adjacent signed quadratic charges on ranks `{floor(n/2), ceil(n/2)}`, with unit layer drop on every reachable
    image and the sorted endpoint, have exact optima `2, 4, 2.695, 4.122` at `n = 4..7`. They need more than `2, 4, 4, 5`.
  - **Barrier, any degree:** a function of a state has range at most the distance in the state quotient. For the central
    witness state that distance is at most `D(n) - 1` at `n = 4..7`.
  - Any function of the single rank `n/2` slice has range at most `D(n/2) + 1` (sort the halves, then a mirror layer). That
    is not a rate bound.
  - **Not ruled out:** ranks `{2, ..., n-2}` certify `D(6)`, `D(7)` (`32/7`, `5.04019`). This is a finite fit of up to 2115
    terms, with no recurrence: a 7-wire baseline lift reaches about 3.63, needing 5. `n = 8` is not refuted (`V <= 39/7`).
  - Evidence: `kahale-signed-charge-screen.md`, `kahale_signed_charge_screen.py`, `kahale_signed_charge_check.py`.
* **Coalition Hall capacity under full reachability (part of LB-25).**
  - Every coalition inequality is automatic (`CongestionBarrier.lean`).
  - Observed deficits (12 zeros into 11 targets) sit in the last layers and may be repeated manifestations of one
    obstruction.
* **Joint observation across a nested hierarchy of cuts (part of LB-26).**
  - It adds no Shannon entropy (`HierarchyRefinement.lean`).
  - Static linear block potentials are redundant (`kahale-rankset-transition.md`).
  - Only weighted or nonlinear inter-scale inequalities remain possible.
* **Adding the counting bound to the Fibonacci bound.**
  - Without a coupled inequality, the result is their maximum: Kahale above `n ≈ 2^33`, counting below
    (`docs/kahale-proof-plan.md` §5; table in `SURVEY.md` (a)).
  - The coupled version is LB-03, rejected above: its true-`h_g` form is LB-26's charging lemma.
* **Shrinking the polynomial factor in `n·F_{d+1} ≤ 2^{d+1}(d+1)^2`.**
  - This improves only the finite error, not the leading coefficient (`docs/kahale-lower-bound.md`).

Parked, not dead:
- LB-22: two-sided certificates. Its per-wire part is dead (LB-02). The pair union-cost part is dead too (LB-24), and
  so are correlation potentials (LB-33), sharpness potentials (LB-35) and mixed-polarity restriction families (LB-34).
- LB-25: congestion rate.
- LB-26: the charging lemma.
- LB-08: quadratic witness charges outside the central band (a finite fit; reopen only with a rule for the weights).
- LB-30: quadratic witness charges, continued as LB-08.
- LB-32: face pair-matrix closure.
