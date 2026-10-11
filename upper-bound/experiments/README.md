# Upper-bound experiments

Keep candidate improvements separate from `../best`. Promote only after checking
the complete sorting guarantee, global depth, and headline axiom dependencies.

- `chvatal/scripts/`: parameter exploration for the current construction.
- `runaware/`: run-aware first column sort (block-merge sorter, 2^29 divisibility, `GenNetwork`
  stage composition); a copy of the former 1770 package. Its design and roadmap are in
  `DESIGN.md` / `ROADMAP.md`. At the two-round column height (m ≈ 2^42) its payoff is only a few
  percent, so it is parked until the larger levers are exhausted.
- `fringe-single-round/`: analysis and scripts for the one-round fringe constants.
- `expanders/`: optional standalone certificate and expander package; native
  evaluation and C FFI are separate from the best proof's trust boundary.

The two-round separator experiment (formerly `tworound*`) was promoted to `../best`.
Research notes about multi-round separators and fringe obstructions are in
`../../docs/`; parked ideas are in `../backlog/`.
