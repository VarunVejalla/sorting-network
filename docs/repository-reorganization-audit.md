# Repository workstream audit

Pre-migration static source and configuration audit, 2026-10-10. The sections
below record the planning snapshot; see the migration note for the final layout. Import reachability is module-level, not a
declaration-level deletion certificate. The local machine-readable inventory
is `LLM-helpers/reorganization-dependencies.json` (gitignored).

## Current best upper package

`chvatal-1830` can become `upper-bound/best` as one complete package. It currently
contains 61 Lean files under AKS (46 Chvatal, 7 Sort, 3 Bitonic, 3 Bounds,
1 Halver, 1 Misc), following further simplification by another agent.
Its guards name the two 1770 endpoints. This audit did not recheck those guards.

All AKS imports resolve inside that package. There are no Random imports or
source imports from the root AKS tree. Mathlib is its sole declared external
Lean package; both root and child toolchains are Lean 4.29.0-rc4.

There is a filesystem coupling: `packagesDir := "../.lake/packages"` shares
the root dependency directory. Moving two levels down requires changing that
path or deliberately choosing a different cache layout, along with checking
the manifest and package-local cache links. Merely moving the source directory
is not a complete migration.

Ten module names also exist in root AKS, and none of those source files are
byte-identical after normalizing line endings. They are two versions of shared
concepts, not ten safe duplicate-file deletions. A standalone best package does
not need to import the old versions. The old versions may still be required by
the lower or alternative-upper packages.

## Import map of the root development

The root has 293 AKS and 40 Random Lean files. Selected transitive local closures:

| Endpoint/work | Local modules | Random dependencies |
| --- | ---: | --- |
| `Bounds.KahaleAsymptotic` | 84 | none |
| `Bounds.PatersonTight` | 187 | none |
| `Seiferas` | 66 | none |
| Conditional/dyadic/additive limit modules together | 71 | none |

The lower-bound coupling is explicit:

`KahaleAsymptotic -> Kahale -> Bounds.Asymptotic -> Bounds.Upper -> Seiferas`.

`Bounds.Upper` defines minimum depth and its basic lemmas in the same module
as the old upper construction. This forces the lower-bound import closure to
include bags, separators, expanders, and Seiferas. Before deleting that upper
stack, extract the minimum-depth foundations and required asymptotic facts
into a construction-independent module, then update and verify lower imports.
The best package's `Bounds.Minimum` illustrates the desired separation, but
its definitions use the best package's evolved network infrastructure; it
cannot simply be mixed with the root package under the same AKS namespace.

The 73 modules in `AKS/Kahale` include substantial exploratory lower-bound work;
only 14 Kahale modules appear in the selected headline endpoint closure.
The others are not therefore obsolete: they require a research-status audit.
Conditional-limit and repair/amplification work belongs to a separate
cross-workstream research area, rather than being discarded as an old bound.

## Random: unnecessary for current bounds, useful optional research

No root AKS module imports Random, and no best-package module imports it.
An old comment in `Random/Concrete/Specific` says Seiferas uses its random base
expander, but the current Seiferas source does not. Follow the source imports.

| Component | Role | Classification |
| --- | --- | --- |
| `Random/Cert.lean`, `Random/Bridge`, `Random/Misc` | Integer certificate checker and proofs transferring certificates to real spectral bounds | Optional reusable expander/certificate research |
| `Random/Concrete` | Concrete graph data, spectral certificates, specializations | Optional examples/base expanders; unnecessary for current bounds |
| `Random/Cert/ReadFFI.lean`, `mmap_string.c` | Runtime certificate loading | Keep only with the certificate package |
| `Random/Bench` | Runtime tests and profiling | Optional maintenance; easiest removal from an active research tree |

The root Lake file nevertheless builds RandomCert, RandomBridge,
RandomConcrete, and RandomMisc by default. RandomBench and its executables
are optional. Thus proof independence does not currently mean independence
of the default root build.

The concrete modules use `native_decide`, and their axiom guards explicitly
record native evaluation axioms. Certificate loading also uses C FFI. This
trust boundary is separate from the standard-axiom headline Chvatal proof.

If retained, keep the certificate ecosystem together: Random, the C external
library target, `rust/certificate.rs`, optional GPU generator,
`scripts/download-certificates`, rotation-data generation, and ignored data.
`Random/Bridge/Read` can download data or invoke Cargo when data is missing;
relocating only Random would leave hardcoded paths broken. Generic spectral
bridge lemmas could later be separated from certificate I/O.

## Proposed disposition

| Material | Recommended home/status |
| --- | --- |
| Current `chvatal-1830` | `upper-bound/best`, intact |
| Completed rounded Paterson stack | `upper-bound/alternatives/paterson`; superseded asymptotic coefficient, useful all-n bound and halver primitives |
| Seiferas/MGG/zigzag stack | `upper-bound/alternatives/seiferas` or archive, after decoupling lower imports |
| Kahale endpoint and retained lower experiments | `lower-bound/best` and `lower-bound/experiments`, after identifying their respective closures |
| Random/certificate ecosystem | Optional `upper-bound/experiments/expanders`, outside default best builds |
| Conditional limit and sorter amplification/repair work | Dedicated `research/limit-existence` area |
| `chvatal-snap`, `chvatal-v`, `.scratch_v`, scratch/tmp | Inspect local differences before removal; they are not a verified duplicate set |
| Generic local automation | Gitignored `LLM-helpers` |
| Handoff | Historical archive or deletion after unique-material review |

Handoff contains 12 files, including Avenue-2 formulas, earlier research
ledgers, and references. They are historically superseded as current status,
but this audit has not established that every mathematical note is duplicated.
No unconditional deletion recommendation is made for them.

## Migration-sensitive infrastructure

Update root/package Lake targets, `AKS.lean` umbrella imports, certificate paths,
generic helper checkout paths, agent guides, READMEs, graph scripts, research
links, and existing worktrees. The comparator CI uses root `Challenge`, root
AKS and `challenge.json`; the sorry gate hardcodes AKS/Random paths. Pages CI
publishes docs directly, so moving docs changes links and possibly publishing.

Recommended sequence: move best as a package; decouple the lower minimum-depth
foundations; create lower best; isolate alternative constructions and optional
certificates; only then deduplicate or remove complete unused groups. Shared
source extraction is optional and should follow explicit compatibility checks.

## Migration note

The implemented layout uses `upper-bound/best`, `lower-bound/best`, separate
experiment packages, and `upper-bound/alternatives/legacy` for the retained
Paterson and Seiferas stack. The lower real-valued liminf endpoint genuinely
uses the legacy logarithmic upper bound to discharge a boundedness premise.
Its finite Kahale inequality does not depend on that construction. Library
names differ across these dependent packages while `AKS.*` module names are
preserved. Unique handoff notes are preserved under `archive/handoffs`.
