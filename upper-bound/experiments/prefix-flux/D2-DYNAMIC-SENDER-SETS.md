# Dynamic sender-set realization of the D2 flow

Status: proposed proof architecture, not yet formalized. It is intended to
replace the difficult equality between routed sets and the canonical
static-hole bags. It does not remove the need for an all-stage spatial
profile invariant or terminal cleanup.

## State and update

At stage `t`, attach to every node `v` of the D2 flow tree an actual finite set
`S_t(v) : Finset (Fin n)` of physical wire indices. Initially the root owns
`Finset.univ` and every other node owns the empty set. The intended size
invariant is

```text
S_t(v).card = d2FlowTreeAllocation 8192 (flow_t(v)).
```

For an active ordinary sender, sort its set in increasing wire-index order
using `orderEmbOfFin`, apply the fixed core on consecutive rank tiles, and
partition the output slots by the already proved parent/child rank ports.
For `topDesc` and `botRise`, use their existing local piece-partition
theorems. For an inactive sender, retain its set as one self piece. Define
`S_(t+1)(v)` to be the union of the pieces targeted to `v`: its retained set
when inactive, the parent down-port when its parent is active, and the up-ports
from active children.

These are actual wire indices: the construction adds no wire permutation.
Each local network is embedded on the sender set by its increasing rank
embedding, so its output-port pieces are subsets of the same physical wires.
The global next-stage partition should follow from the local piece partitions
and `routed_local_destinations_preserve_partition` in
`D2OrdinaryRankRouting.lean`.

## Flow-size induction to prove

The initial size statement follows from `d2FlowTreeAllocation_initial`.
For each transition, prove the receiver-set cardinality equals the updated
flow allocation:

- An active node has no active adjacent node in the candidate schedule, sends
  its whole current set to its neighbors, and has zero post-stage allocation.
- An inactive node keeps its current set and receives the parent's down-port
  and its active children's up-ports. Its new allocation is the old
  allocation plus exactly these incoming port lengths; parent root-overwrite
  cases are included in the down-port term.

Prove this by induction on tree height, using the flow's existing root/child
update equations and the role-specific local partition/cardinality lemmas.
Handle the startup stages and root boundary separately. Do not use static-hole
fit or identify the resulting sets with `d2FlowNodeStaticBag`.

## Why this may simplify the profile bridge

The source pieces are now the definition of the receiver tags. Their global
disjointness and coverage are combinatorial consequences of the local port
partitions. The arbitrary-set complete-tile identity in
`D2ClippedCellRankInterval.lean` already uses `orderEmbOfFin`; the clipped
physical profile transfer in `D2PhysicalFlowProfileTransfer.lean` supports
partial row heights `m <= 4096`. These interfaces can be applied to the
dynamically constructed sender sets without proving the static interval
recurrence in `flow_dag.py` inside Lean.

With each sender ordered by increasing physical wire index, every comparator
is ascending between its two physical indices. Thus each stage preserves or
increases the global zero count on every physical prefix. The remaining
analytic task is still to bound the spatial prefix defect (or a stronger
distance-sensitive potential) tightly enough at the terminal stage; total
sender-set cardinalities and aggregate error alone do not imply sorted output.

## First decisive Lean milestone

Add a layout datatype mirroring `D2FlowTree`, storing one sender `Finset` at
each node. Prove a one-stage theorem that, under the candidate activity and
role callbacks plus the existing flow input contracts, (1) all next sender
sets are pairwise disjoint and cover `Finset.univ`, and (2) every next set has
cardinality equal to the corresponding node's `d2FlowTreeAllocation` after
`d2FlowStage`. Include the `topDesc`, `botRise`, and parent-overwrite cases.
If this theorem is materially harder than the static-bag identity, or its
cardinality recurrence fails for a reachable case, reassess this architecture
before building more profile lemmas on it.
