# Upper-bound experiments

Keep candidate improvements separate from `../best`. Promote only after checking
the complete sorting guarantee, global depth, and headline axiom dependencies.

- `chvatal/scripts/`: parameter exploration for the current construction.
- `expanders/`: optional standalone certificate and expander package; native
  evaluation and C FFI are separate from the best proof's trust boundary.

Research notes about multi-round separators and fringe obstructions are in
`../../docs/`. A small local primitive is not itself a better sorting bound.
