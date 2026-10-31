# Sub-300 goal

Prove, with a complete kernel-checked argument, that

```text
limsup D(n) / log2(n) < 300,
```

where `D(n)` is the minimum depth of a binary-comparator sorting network on
`n` wires.

Follow [`sub300-work-plan.md`](sub300-work-plan.md) for priorities and working
rules. Start each resumed session with the current
[`prefix-flux handoff`](../upper-bound/experiments/prefix-flux/HANDOFF.md),
then inspect only the sources needed for its next proof gate. Keep mathematical
claims and evidence levels explicit; commit coherent source and handoff
milestones. Do not claim the goal is achieved until the full all-size theorem
passes the repository's contribution checks.
