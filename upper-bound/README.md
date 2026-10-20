# Upper bounds

`best/` contains the current best kernel-checked upper bound in this repository:

```text
limsup D(n) / log₂ n ≤ 789.75
```

It is a self-contained Lean package. The 789.75 proof (UB-31, `best/AKS/Sub800/`) runs a
Chvátal-style tree at (k, A, ν) = (16, 32, 1/8) with the deficit flow table "design P", the
walk-bound two-round separator on rows < 2^26 and a padded fringe separator; it reuses the
package's Chvátal modules. See [`best/README.md`](best/README.md) for the finite bound, proof map,
and build instructions.

The previous best (Chvátal with a two-round separator, 1419) is kept in `alternatives/chvatal-1419/`,
and the one before (one-round separator, 1770) in `alternatives/chvatal-1770/`.
The ticketed research backlog is in [`backlog/README.md`](backlog/README.md); it includes
ordinary-node sorter depth, smaller node windows, partial sorting, schedule optimization, and
expander/halver alternatives, with a new ticket for the 2024 k-sorting construction and its
preliminary screen in [`experiments/k-sorting-2024`](experiments/k-sorting-2024/README.md).
Older exploratory work is kept separately in `experiments/`
(promote to `best/` only after the full build, the axioms guard and the headline are checked).
For independent end-to-end proofs using the canonical network model and `D(n)`, start at
[`contributions/README.md`](contributions/README.md).
