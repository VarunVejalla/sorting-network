# Chvátal proof inventory and consolidation

Inventory of `chvatal-1830/AKS/` on 2026-10-09, after promoting the verified pruning fixed point. Dependencies, build artifacts, scripts, and other packages are excluded.

## Source declarations

| Kind | Count |
| --- | ---: |
| `theorem` | 558 |
| `lemma` | 42 |
| `def` | 199 |
| `abbrev` | 5 |
| `structure` | 25 |
| `instance` | 5 |
| **Total** | **834** |

There are **88 Lean files**. There is also one local tactic macro (`act` in
`FlowTable.lean`), excluded from the logical declaration total. There are no
source `inductive`, `opaque`, `axiom`, or `constant` declarations.

These are written source declarations, not compiled environment constants.
Structure fields, constructors, generated recursors, equation lemmas, and local
`have` bindings are excluded. Inline attributes and declaration modifiers are
handled; comments are removed before counting. `theorem` and `lemma` have the
same logical role but are counted by their source keyword.

## Lines

| Mutually exclusive category | Lines |
| --- | ---: |
| Contains code | 11,299 |
| Documentation comments only (`/--`, `/-!`) | 766 |
| Ordinary comments only | 250 |
| Blank or whitespace only | 1,557 |
| **Total physical lines** | **13,872** |

Of the code lines, 19 also contain comments; they are counted once, as code.
“Code” includes imports, namespace/section commands, attributes, definitions,
statements, and proofs. Nested block comments and quoted strings are recognized.
Comment-only lines with documentation and ordinary comment text are classified
as documentation. Whitespace-only lines inside comments remain whitespace.

PowerShell's `Measure-Object -Line` gives **12,316**: it excludes the 1,556
completely empty lines but includes the one nonempty whitespace-only line.

The read-only counting helper and local build logs are in the gitignored
`LLM-helpers/` directory on this workstation.

## Next consolidation steps

1. Review the declaration graph regenerated on 2026-10-09. It contains 1,060
   compiled declarations: 943 reachable and 117 unreachable from the two headline
   theorems, with 8,603 distinct dependency edges (11,702 recorded edges before
   deduplication). Generated helpers explain the larger count than the source
   inventory. Proof-term reachability alone does not justify deleting
   tactic references, instances, attributes, or elaboration support.
2. Generalize finite-set rank/window counting across ordered key types.
   `BadSendReal.BW.rankN` works on naturals while `WireFlow.rankIn` works on `Fin`;
   the source explicitly identifies the former as a copy. A common counting
   interface could remove duplication without changing the scheduler.
3. Consolidate repeated filter/cardinality and cast arguments in the matrix
   pipeline (`MatrixBridge`, `SortedColumnDecode`) and natural flow allocation
   (`FlowSizes7`). Prefer reusable counting lemmas over broad `simp` calls.
4. Keep the parity-rounding step interface in `Schedule7`. Expanding rounding
   and floors into a single `omega` call failed in the interrupted simplification;
   the restored modular lemmas compile.
5. Review small, single-purpose wrapper modules for mergers after reachability
   analysis. The final theorem imports 87 of 88 modules transitively; the remaining
   module is its axiom guard. Module reachability does not imply that every
   declaration in those modules is needed.

The largest files are `SortedColumnDecode` (749 lines), `MatrixBridge` (538),
`FlowSizes7` (475), `BadSendReal` (437), and `FlipSpec` (416). These are review
priorities, not claims that their mathematical content can be discarded.

The earlier ledger is a historical assembly record. Some old obligations and
module references there were superseded by the completed proof and simplification.

## Generated graph artifacts

`chvatal-1830/scripts/data/decls.txt` records source ranges and reachability;
`edges.txt` records project dependency edges. Local `summary.json` records counts,
roots, and SHA-256 hashes of all 88 source files. These files are ignored generated
artifacts; regenerate them with `lake env lean scripts/usage.lean` from the package
directory after source changes. The older `keep.txt` belongs to the previous
pruning run and is not a freshly audited deletion whitelist.

The exporter now rejects missing roots and restricts traversal to project
declarations: imported Lean and Mathlib modules precede AKS and cannot depend on
its declarations. The headline axiom-guard target also passed on 2026-10-09.

## Promoted pruning baseline

The automated deletion loop reached a fixed point and removed 20 written
declarations and 136 physical lines across six files. The two headline theorem
statements, axiom guards, and minimum-depth definition were preserved. Remaining
failed candidates are still referenced by tactic code; further deletion requires
proof changes. The fixed point concerns these candidate and batching rules, not
all possible proof simplifications.
