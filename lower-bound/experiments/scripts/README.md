# Lower-bound probes

Run these Python scripts from the repository root. Their default input and
output paths still refer to root `docs/`, so relocation does not change the
saved witness locations. For example:

```sh
python lower-bound/experiments/scripts/kahale_boundary_information.py --help
```

These are exploratory computations, not substitutes for the Lean endpoint.

The current joint routing-group probe is `kahale_joint_groups.py`; it checks
conditional certificate cores, activation-graph updates, and shortest-layer
completion profiles on complete small catalogues. `kahale_joint_slice_sat.py`
screens a shared layer schedule on neighboring input-weight slices using
the locally installed Z3; timeouts are inconclusive and UNSAT reports are
not kernel checked. See `docs/kahale-joint-groups.md` at the repository root.

`kahale_activation_scales.py` extends the graph model to minimal activation
hypergraphs of every order. It checks exact AND/OR updates and certificate
duality, then screens weighted transversal potentials with numerical SciPy
linear programs. See `docs/kahale-activation-scales.md`; fitted finite growth
rates are not asymptotic lower-bound coefficients.

`kahale_sorted_block_activation.py` gives exact certificate-growth counts
for a parallel aligned layer on two sorted blocks. The derived limiting
ratio is `3/2`, an obstruction to a one-layer rate bound on full certificate
cost; it does not rule out charging block preparation.

`kahale_certificate_preparation.py` checks repeated certificate-growth
spikes in depth-logarithmic aligned prefixes with exact rational recursion,
plus small independent truth-table checks. `kahale_fixed_antichains.py`
compares fixed-input order antichains with unrestricted cubes in the actual
Boolean output image of equal-height prefixes. See
`docs/kahale-certificate-preparation.md` for the amortization barrier and
the derived family-specific suffix bound.

`kahale_image_difficulty.py` completely enumerates reachable Boolean
images and exact completion distances through five wires. It screens
unrestricted cubes, rank-decision supports, and simultaneous dependency
cones, and saves explicit failures of additive cube/gathering bounds.
See `docs/kahale-image-difficulty.md` for the joint obstruction and the
limits of dependency-only relaxations.

`kahale_joint_polarity.py` compares inversion-signature quotient bounds
with exact residual distances and verifies shared AND/OR transport via
mixed witnesses. It saves an ordered-prefix nonclosure counterexample.
See `docs/kahale-joint-polarity.md`; the transport is between witness
orders, not a fixed-order closure or an asymptotic improvement.

`kahale_witness_charge.py` screens amortized additive and quadratic
potentials over the complete image catalogues. It rationalizes SciPy
solutions and checks primal and dual certificates exactly. See
`docs/kahale-witness-charge.md` for the additive barrier, nonlinear finite
escape, and the missing scale-compatible inequality.
