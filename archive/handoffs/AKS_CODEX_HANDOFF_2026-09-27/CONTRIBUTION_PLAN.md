# Recommended Contribution Plan for the Local `girving/aks` Clone

## Track 0 — Establish the baseline

Before changing mathematics:

```bash
lake exe cache get
lake build AKS
```

Read:

```text
README.md
CLAUDE.md
AKS/Seiferas.lean
AKS/Bags/Params.lean
AKS/Bags/Depth.lean
AKS/Halver/Defs.lean
AKS/Halver/FromExpander.lean
AKS/Separator/Defs.lean
AKS/Separator/FromHalver.lean
```

Then trace exactly:

```text
local primitive depth
→ separator depth
→ Params.depth / stagesFactor
→ seiferasParams_depth_le
→ network_depth_le
```

Create a short local note with the exact Lean names in the checked-out revision.

---

# Track 1 — Low-risk constant reductions in the existing architecture

These are useful even before Paterson is formalized.

## 1A. Optimize the current `Params`

The repo parameter constraints are explicit rational inequalities.

Write a small external search program or Lean evaluator over rational candidates for

\[
(\gamma,\varepsilon,\nu,A)
\]

subject to all fields of `Params`.

Objective: minimize the actual expression feeding `Params.depth`, not merely one individual inequality.

The current huge halver depth will probably dominate, so do not expect parameter search alone to make the final constant good.

## 1B. Fewer MGG squarings / tighter spectral accounting

The README explicitly identifies six squarings as the primary blow-up.

Audit:

- exact spectral inequality used;
- exact halver error required by current separator parameters;
- whether different `ε` / `γ` choices permit fewer squarings;
- whether the MGG spectral bound is unnecessarily loose;
- whether a different powering/spectral argument helps.

Even reducing six squarings to five changes the degree exponent dramatically.

## 1C. Improve `Separator/FromHalver`

The current construction pays one full halver-family depth per separator level:

\[
\text{separator depth}\le t\cdot\text{halver depth}.
\]

Check whether Paterson or Chvátal supplies a direct separator construction with a better depth/error tradeoff than prefix-doubling an ε-halver.

This may be an easier intermediate contribution than formalizing all of Paterson.

---

# Track 2 — Paterson 1990 formalization (recommended major first contribution)

Paper:

> Michael S. Paterson, *Improved Sorting Networks with O(log N) Depth*, Algorithmica 5 (1990), 75–92.

The repo README itself cites this as a route to `<6100 log n`.

## Step 2.1 — Extract the exact constructive theorem

Do not start coding until the paper's interfaces are written down precisely.

For every local network Paterson uses, record:

- input arity;
- exact property (halver? separator? nearsorter?);
- error parameter;
- depth;
- divisibility/power-of-two assumptions;
- whether existence is probabilistic or explicit;
- whether the network is uniform for all sizes;
- whether the theorem already has a form close to `HalverFamily`.

Produce `docs/paterson_interface.md` locally.

## Step 2.2 — Decide the reuse boundary

There are three possible integration strategies.

### Strategy A: Paterson → `HalverFamily`

Best case.

Implement e.g.

```text
AKS/Halver/Paterson.lean
```

with a theorem producing

```lean
HalverFamily ε
```

at much smaller `depth`.

Then reuse:

```text
Separator/FromHalver
Bags/*
Seiferas.lean
```

Advantages:
- minimal disturbance to the existing trusted proof;
- immediately produces a new explicit top-level constant;
- easiest upstream PR.

### Strategy B: Paterson → direct separator family

If Paterson's useful primitive is stronger than an ordinary halver and the current halver→separator conversion loses too much, create a direct separator implementation satisfying whatever interface `Bags/` consumes.

This may give a much better constant while still reusing the whole bag-tree proof.

### Strategy C: formalize Paterson's entire global construction

Only prefer this if Paterson's global architecture cannot efficiently plug into the current Seiferas abstractions.

This has more proof work, but the published/repo-reported `<6100 log n` constant is then a clear target.

## Step 2.3 — Keep numerical theorems modular

Aim for the structure:

```text
paterson_local_correctness
paterson_local_depth_le
patersonHalverFamily
patersonSeparatorFamily
patersonParams
patersonParams_depth_le
paterson_network_depth_le
```

so future improvements can change one layer without rewriting the whole proof.

## Step 2.4 — Recompute the constant by kernel

Do not hard-code a claimed 6100 unless the formal parameter chain proves it.

Let Lean reduce/check the final rational/integer inequality, in the same style as the current `by decide +kernel` bounds.

---

# Track 3 — Use Chvátal / AKS-1992 to improve local primitives

This is a second known-literature track.

Useful source ideas:

- Chvátal's explicit separator Properties B/F;
- AKS 1992 depth-2 large-sorter halvers;
- direct multiway partitioning instead of binary recursive splitting.

Potential formal target:

```text
stronger separator / multiway splitter
→ Seiferas-like bag update
→ smaller local-depth/error tradeoff
```

This may outperform a plain Paterson halver while remaining within known mathematics.

---

# Track 4 — Novel Avenue-2 `GoodSplitter` research

Only start this after the known-path work is well understood.

## Desired abstraction

Something conceptually like:

```lean
structure GoodSplitter where
  depth : Nat
  net : ...
  bulk_bound : ...
  ordinary_fringe_bound : ...
  nested_safe_fringe_bound : ...
```

The exact Lean interface should be designed from the theorem that consumes it, not from the old handoff notation.

## Main research challenge

Use only enough multiscale correction to guarantee:

\[
q\phi=O(1),
\quad
\psi=O(1),
\quad
\eta=O(1),
\quad
q\asymp p^2,
\]

without continuing until exact rank classification.

If successful, derive a binary depth

\[
S(p)\le (a+o(1))\lg p
\]

with \(a\) strictly less than the effective full-sort constant per three rank bits.

Then plug into the global scheduler.

## What would count as genuine progress

A theorem of the form:

\[
\text{after }c\lg p\text{ Seiferas/Paterson-style stages},
\]

the selected outer/coarse/fine rank regions obey exactly the three `GoodSplitter` error bounds, with

\[
c<c_{\rm exact}.
\]

This would show that approximate local classification is genuinely cheaper than full sorting.

---

# Suggested work ordering

1. Build current repo.
2. Write exact constant dependency map.
3. Parameter-search current architecture.
4. Read Paterson and write exact theorem/interface extraction.
5. Implement the easiest Paterson primitive that plugs into existing abstractions.
6. Produce a new kernel-checked final constant.
7. Upstream that contribution.
8. Only then resume the new `GoodSplitter` theorem unless a very clear shorter route appears.

This order maximizes the chance of producing a useful contribution even if the novel research direction stalls.
