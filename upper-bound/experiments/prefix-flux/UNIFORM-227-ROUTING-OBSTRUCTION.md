# Uniform-U address-flow obstruction

2026-10-21. The 227.5 candidate's local separator contract is not enough to
support the usual exact-address terminal invariant. The existing perfect-
separator simulator finds wrong-address keys at the end of the actual uniform
U schedule, even when every active node performs the ideal rank-ordered split.

## Reproduction

Run:

```text
python upper-bound/experiments/prefix-flux/uniform_227_routing_obstruction.py
```

For `(x,y,z)=(3,2,2)`, depth `d=5`, and deterministic seed `1`, the uniform
U table has five scheduled stages. After the last stage it leaves 1,280 keys
in level-3 nodes whose address `key // 64` differs from the node index; the
worst terminal node has `wrong/cap = 0.078125`. The same script run on the D2
cut-layout table with the identical parameters, depth, and seed leaves zero
wrong-address keys. The test uses exact integral flow quotas and the actual
`build_table` scheduler, not a rounded geometric approximation.

The experiment is scale-homogeneous: multiplying every flow count and key
interval by `S=2^14` preserves every split ratio and lifts the discrepancy to
`1280*S` keys with the same worst-node fraction. Thus the scale used to obtain
the candidate's exact local rectangles does not remove this address defect.

## What this does and does not show

This is a counterexample to the claim that the U flow routes every rank into
its designated terminal subtree under ideal local rank splits. It blocks a
zero-error address-preservation induction for the current uniform-U schedule,
and explains why the global proof cannot be supplied by the screened local
F2 bounds alone. It is not a counterexample to an actual comparator network:
the current separator hypotheses allow nonzero local defects, and a new
coupled rank/address invariant could in principle show that those defects
correct the U flow's deterministic address mismatch. Such a compensation
claim needs a precise recurrence and terminal-purity proof; none is known.

The D2 control is instructive: its variable cut-layout blocks eliminate this
exact mismatch. Any route retaining small row sorts and the 227.5 stage price
should therefore test a D2-like nonuniform routing table, not simply improve
the B2/F2 provider for uniform U. That alternative still faces the
small-row bulk and fringe-provider gates and requires new exact geometry.
