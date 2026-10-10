# AKS / Sorting-Network Constant Project — Codex Handoff

**Date:** 2026-09-27  
**Target repository:** `https://github.com/girving/aks`  
**Assumption:** the user has already cloned that repository locally and will give this package to Codex in that working tree.

## One-sentence objective

Use the existing Lean formalization in `girving/aks` as the base for improving the explicit constant in

\[
D(n) \le C \lg n + O(1)
\]

for ordinary binary-comparator sorting networks, ideally first by a conservative Paterson-based improvement and later, if worthwhile, by formalizing our more aggressive approximate-splitter / Avenue-2 ideas.

## Read these first

1. `CODEX_PROMPT.md` — the shortest operational prompt for Codex.
2. `GIRVING_AKS_REPO_MAP.md` — what the current repository already proves and where the constant comes from.
3. `PROOF_STATUS_LEDGER.md` — what is actually established versus provisional or rejected.
4. `CURRENT_RESEARCH_STATE.md` — the mathematical context from this conversation.
5. `CONTRIBUTION_PLAN.md` — recommended work order.
6. `REFERENCES_AND_LINKS.md` — papers and URLs.
7. `prior_handoffs/` — earlier detailed project handoffs. They contain more derivations, but several old candidate constants were later found to have gaps; use the proof-status ledger when interpreting them.

## Critical warning

Do **not** assume that every attractive constant in the prior handoffs is proved.

In particular:

- the old \(24+o(1)\) \(M\)-sorter structural theorem was a **candidate**, not an established theorem;
- the later roughly-\(40\) four-pass repair was also **provisional**;
- the current Avenue-2 `GoodSplitter` / `LocalFunnel` work is a research program, not yet a complete sorting theorem;
- several simpler approaches were explicitly rejected after exact auditing.

The safest concrete contribution to `girving/aks` is therefore:

> improve the local halver/separator implementation, especially by formalizing Paterson's 1990 construction or a quantitatively better primitive, while reusing the repository's already-formalized Seiferas bag-tree correctness proof.

## Baseline repository facts checked on 2026-09-27

The repository README currently states:

- top-level theorem:
  \[
  (\mathrm{network}\ n).\mathrm{depth}
  \le 141\cdot 10^{62}\,\lceil\lg n\rceil;
  \]
- current proof path:
  `MGG expander → repeated squaring → ε-halvers → (γ,ε)-separators → Seiferas bag tree`;
- six graph squarings turn degree \(8\) into \(8^{64}\), which is the dominant source of the astronomical constant;
- the repository itself lists Paterson's 1990 construction (`< 6100 log n`) and Seiferas's much smaller reported constants as obvious improvement directions.

The current concrete Seiferas parameters in `AKS/Bags/Params.lean` are:

\[
\gamma=\varepsilon=\frac1{100},\qquad
\nu=\frac{13}{20},\qquad
A=10.
\]

The theorem `seiferasParams_depth_le` in `AKS/Bags/Depth.lean` currently proves

\[
\mathrm{seiferasParams.depth}\le 141\cdot10^{62},
\]

and the file also proves a lower bound of \(140\cdot10^{62}\) on that same concrete quantity, so the present enormous value is not merely a loose final arithmetic inequality: it is baked into the current local primitive/parameter instantiation.

## Recommended first command

From the repo root:

```bash
lake exe cache get
lake build AKS
```

Do **not** start with bare `lake build` unless you want the optional `Random/` certificate path; the README warns that this can pull multi-gigabyte certificate data.

## User's preference / research style

The objective is not merely to reproduce known AKS asymptotics. The user wants the explicit constant as small as possible and is happy to pursue new mathematics if needed. However, every claimed improvement should be separated into:

1. proved in the existing repo,
2. proved on paper / source-backed but not formalized here,
3. derived in this conversation but not independently audited,
4. speculative.

The repository contribution should preserve that distinction.
