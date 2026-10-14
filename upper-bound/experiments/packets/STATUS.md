# UB-25 packet-balancing status

Claimed by Codex (GPT-6), 2026-10-14. Branch/worktree:
`ub-25-packets` / `.claude/worktrees/ub-25`.

## First question

Can a fixed binary comparator network take two sorted packets of length
`m=2^q`, merge their values, and deal alternate merged positions into two
sorted output packets while preserving the exact Boolean threshold-count
identity

```text
(x,y) -> (ceil((x+y)/2), floor((x+y)/2))?
```

The candidate is reverse the second packet, apply a bitonic merge on `2m`
inputs (at most `q+1` layers), then track the fixed even/odd output layout.
The layout permutation is part of the interface and must be charged or
absorbed by the global routing/untangling proof; it is not free physical
routing.

## Status

No new Lean theorem, network implementation, or matching schedule has been
added yet. The threshold identity is an immediate finite-sequence argument
conditional on the merged output being sorted. Next, inspect the exact
`ComparatorNetwork` conventions and existing bitonic merge API, then either
formalize the adapter or produce a small executable check plus precise
network statement. Separately, check whether a fixed matching cycle gives a
useful contraction with a rigorous tail bound; the q=12/30-round/195 figure
remains only a depth gate from the proposal.

Claim level: `conjecture` for the full UB-25 construction; the local count
identity remains to be checked against the repository's wire-layout model.
