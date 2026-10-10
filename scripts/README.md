# Repository scripts

Run root maintenance scripts from the repository root. The root Lakefile now
contains only the shared Mathlib dependency and cache context; it has no Lean
libraries or executables. `lake build AKS` and certificate targets therefore
belong to a package directory, not the root.

## Where Lean commands run

- Current upper-bound proofs: `upper-bound/best`
- Current lower-bound proofs: `lower-bound/best`
- Historical Seiferas/Paterson code and its dependency analysis: `upper-bound/alternatives/legacy`
- Optional graph and certificate experiments: `upper-bound/experiments/expanders`

Each package has its own Lakefile and uses the repository's cached Mathlib
checkout. Enter the package directory before invoking `lake build`, `lake exe`,
or a helper that runs Lake. In particular, certificate data, Rust inputs, and
helper scripts are resolved relative to the expander package directory.

## Root maintenance tools

- `scripts/sorry-gate` and `scripts/sorries` scan protected/source files across
  active workstreams; they do not compile Lean.
- `scripts/large [PATH]` reports large Lean source files, defaulting to
  `upper-bound/best/AKS`. It prunes `.lake`, `data`, and `archive` directories.
- `scripts/update-viz-lines` and `scripts/viz-edges` maintain the proof
  visualization. Both resolve historical `AKS/...` paths against the current
  packages, preferring `upper-bound/best`; `Random/...` resolves in the
  expander package. `viz-edges` reads `tmp/deps.txt` at the repository root
  when present and otherwise falls back to source references. Generate Lean
  dependency data from the package whose modules are being analyzed.
- `scripts/extract-history` updates the historical proof-status visualization.
- `scripts/test-olean-size.py` is a standalone Lean serialization experiment;
  it runs from the root environment and does not import project modules.
- `scripts/lean-search` queries the external LeanSearch service.

The old dependency graph utility and sibling-native simulation now live under
`upper-bound/alternatives/legacy/scripts`. Certificate-specific helpers,
including `bench` and `onesided_verify_experiment.py`, live under
`upper-bound/experiments/expanders/scripts`.
