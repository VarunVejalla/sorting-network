# Prompt for Codex

You are working in a local clone of:

`https://github.com/girving/aks`

Read this handoff package first, especially:

- `README_START_HERE.md`
- `GIRVING_AKS_REPO_MAP.md`
- `PROOF_STATUS_LEDGER.md`
- `CURRENT_RESEARCH_STATE.md`
- `CONTRIBUTION_PLAN.md`
- `REFERENCES_AND_LINKS.md`

Then inspect the actual local repository, especially:

- `README.md`
- `CLAUDE.md`
- `AKS/Seiferas.lean`
- `AKS/Bags/Params.lean`
- `AKS/Bags/Depth.lean`
- `AKS/Halver/Defs.lean`
- `AKS/Halver/FromExpander.lean`
- `AKS/Separator/Defs.lean`
- `AKS/Separator/FromHalver.lean`

First reproduce the current core build with:

```bash
lake exe cache get
lake build AKS
```

## Main objective

Improve the explicit constant in the formal theorem

\[
D(n)\le C\lceil\lg n\rceil
\]

as much as possible, ideally contributing improvements upstream.

## Preferred first research track

Before attempting the novel Avenue-2 construction, investigate formalizing **Mike Paterson, "Improved Sorting Networks with O(log N) Depth", Algorithmica 5 (1990), 75–92** inside this repo.

The repo itself cites Paterson and says his construction achieves depth `< 6100 log n`.

Determine whether the easiest contribution is:

1. a Paterson-style `HalverFamily` that plugs into the existing `Separator/` and `Bags/` machinery;
2. a stronger Paterson separator primitive that bypasses `Separator/FromHalver.lean`;
3. or a separate Paterson global network formalization.

Prefer reuse of the existing Seiferas bag-tree correctness proof if the interfaces line up.

## Important constraints

- Do not silently treat the old \(24+o(1)\) or provisional \(\sim40\) Avenue-1 coefficient as a theorem.
- Do not silently use the rejected argument "ordinary halver prefix bounds imply geometric displacement tails."
- Do not recurse exact sorters blindly; the Avenue-2 motivation was precisely to avoid a noncontractive recurrence.
- If you improve the constant, track the dependency all the way to `AKS/Seiferas.lean` and make the final numeral kernel-checkable.
- Keep the proof trusted in the same sense as the core `AKS/` tree if possible; avoid depending on the optional huge `Random/` certificate path unless there is a compelling reason.

## Useful near-term deliverable

A very good first milestone is:

> a new formally proved local primitive (preferably Paterson-based) satisfying the repository's `HalverFamily` or separator interface, together with an explicit numerical recomputation of the resulting `Params.depth` and top-level `network_depth_le`.

Even if the resulting constant is still in the thousands, reducing \(1.41\times10^{64}\) by dozens of orders of magnitude would be a meaningful upstream contribution.
