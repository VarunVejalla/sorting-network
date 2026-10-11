# Upper bounds

`best/` contains the current best kernel-checked upper bound in this repository:

```text
limsup D(n) / log₂ n ≤ 1419
```

It is a self-contained Lean package based on Chvátal's construction with a two-round
(sort, scramble, sort, scramble, sort) separator at column height 2^42 < m ≤ 2^43. See
[`best/README.md`](best/README.md) for the finite bound, proof map, and build instructions.

The previous best (one-round separator, 1770) is kept in `alternatives/chvatal-1770/`.
Parked ideas, including the research track for a few-hundred coefficient and a list of ideas
already ruled out, are in `backlog/`. Exploratory work is kept separately in `experiments/`
(promote to `best/` only after the full build, the axioms guard and the headline are checked).
