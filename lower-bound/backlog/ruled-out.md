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
  - Only signed **quadratic** cross-image charges escape, and those are parked as LB-08.
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
  - The coupled version is LB-03.
* **Shrinking the polynomial factor in `n·F_{d+1} ≤ 2^{d+1}(d+1)^2`.**
  - This improves only the finite error, not the leading coefficient (`docs/kahale-lower-bound.md`).

Parked, not dead:
- LB-22: two-sided certificates. Its per-wire part is dead (LB-02); the cross-wire part continues in LB-24.
- LB-24: pair union costs.
- LB-25: congestion rate.
- LB-26: the charging lemma.
- LB-30: quadratic witness charges, continued as LB-08.
- LB-32: face pair-matrix closure.
