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
