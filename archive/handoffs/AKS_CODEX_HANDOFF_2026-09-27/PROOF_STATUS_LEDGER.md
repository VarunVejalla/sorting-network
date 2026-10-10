# Proof-Status Ledger

This is the most important file for avoiding false starts.

| Item | Status | Notes |
|---|---|---|
| `girving/aks` top-level \(141\cdot10^{62}\lg n\) bound | **Formally proved in repo** | Kernel-checked Lean theorem on current public branch. |
| Current concrete Seiferas parameters \(\gamma=\epsilon=1/100,\nu=13/20,A=10\) | **Formally present in repo** | `AKS/Bags/Params.lean`. |
| Current huge constant caused mainly by six MGG graph squarings / huge degree | **Repo-documented** | README explicitly identifies this. |
| Paterson 1990 \(O(\log n)\) sorting construction; repo says `<6100 log n` | **Published / repo-cited, not formalized in this repo** | Primary near-term formalization target. |
| Chvátal explicit 1830 construction | **Published/source-backed** | Separate known explicit construction; not the current repo path. |
| AKS 1992 depth-2 large-sorter halvers / multiway partition idea | **Published/source-backed** | Useful for stronger local-splitter research. |
| Old conversation candidate \(D_M(n)\le(24+o(1))\log_M n\) | **NOT proved** | Hidden global-transition losses were later found. |
| Provisional repaired Avenue-1 coefficient around \(40+o_M(1)\) using four passes | **NOT proved** | Treat as a research lead only. |
| p-ary register reassignment formulas and safe-fraction geometry from old handoff | **Derived carefully but not Lean-formalized** | More reliable than the global theorem, but still our derivation. |
| `GoodSplitter` abstraction and global depth formula | **Derived / design abstraction** | Useful interface; not a published theorem. |
| Naive recursive exact-sorter substitution is noncontractive | **Established asymptotic obstruction** | Motivates Avenue 2. |
| Self-recursive splitter recurrence contracts if \(\sum a_j\alpha_j<1\) | **Elementary derived criterion** | Conditional on constructing such a splitter. |
| Replacing exact sorters by weak splitters inside old sort→scramble→sort proof | **Rejected** | Canonicalization/output-entropy obstruction. |
| Three-pass Zig–Zag–Zig automatically gives simple \(E_r^+\le E_{r+1}+\delta E_{r-1}\) | **Rejected** | Arbitrary bookkeeping can cost +2 wrongness. |
| Ordinary halver prefix guarantee automatically gives geometric displacement tail | **Rejected** | Explicitly identified as an invalid shortcut. |
| Ad hoc repeated `EdgeRepair` with amplified error alone is enough | **Rejected/incomplete** | Does not control newly created first-order sibling-crossing strangers. |
| Seiferas per-bag stranger invariant handles fresh 1-strangers | **Published and formalized in repo** | Strong reliable foundation. |
| Conversation derivation: running Seiferas to subunit capacity at a target depth gives exact rank-pure cells | **Derived, not separately formalized** | This is essentially an exact sorter in disguise and not useful for Avenue 2. |
| Current true Avenue-2 frontier: stop earlier and prove only `GoodSplitter`-strength approximate guarantees | **OPEN** | Novel research problem. |

## Things Codex should not resurrect without a new proof

1. Current-scale-only aligned/shifted windows giving a tiny coefficient.
2. Naive \(8\), \(12\), or \(24\) binary constants.
3. “Halver prefix bounds imply exponential physical displacement.”
4. Blind recursion of the full sorting theorem.
5. Treating the Margulis/MGG expander as mathematically essential. It is only the current repo's convenient explicit expander source.

## Confidence hierarchy

When deciding what to implement first:

1. **Highest confidence:** existing Lean repo + published Paterson/Seiferas/AKS/Chvátal results.
2. **Medium:** clean elementary recurrence calculations and local geometric lemmas from our handoffs.
3. **Lower:** unpublished global p-ary constructions and `GoodSplitter` architecture.
4. **Exploratory:** any new numerical constant not yet formalized or independently checked.
