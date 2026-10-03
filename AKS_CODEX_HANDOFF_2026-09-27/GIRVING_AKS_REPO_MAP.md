# `girving/aks` Repository Map and Constant Bottleneck

Repository: `https://github.com/girving/aks`

This reflects the public `main` branch as checked on 2026-09-27. Codex should verify the local clone in case it differs.

## Top-level theorem

`AKS/Seiferas.lean` assembles the construction. The current theorem is

\[
(\mathrm{network}\ n).\mathrm{depth}
\le 141\cdot10^{62}\cdot \mathrm{Nat.clog}\ 2\ n.
\]

For `n < 1024`, the implementation uses a bitonic network. For larger `n` it uses `seiferasNetwork seiferasParams`.

The main proof stack is:

```text
Margulis–Gabber–Galil (MGG) expander
    ↓ graph squaring
ε-halver
    ↓ prefix-doubling / iterated halving
(γ, ε)-separator
    ↓
Seiferas bag-tree sorting
    ↓
top-level O(log n)-depth sorting network
```

## Why the constant is huge

The README explicitly identifies the dominant blow-up:

- base MGG expander has degree 8;
- the available spectral-gap bound is too weak for the required halver error;
- the graph is squared six times;
- degree becomes
  \[
  8^{2^6}=8^{64}\approx 6.3\times10^{57};
  \]
- expander-to-halver depth is bounded by that degree;
- this then propagates through separator and bag-tree depth accounting.

So the astronomical constant is mostly a consequence of a clean, explicit, certificate-free expander route, not a fundamental AKS lower limit.

## Relevant directories

```text
AKS/
  Seiferas.lean          top-level assembly
  Sort/                  comparator networks, zero-one principle, monotonicity
  Bitonic/               Batcher bitonic sort
  Graph/                 regular graphs, spectral gap, squaring
  MGG/                   Margulis–Gabber–Galil expander
  Halver/                ε-halvers and expander→halver bridge
  Separator/             (γ,ε)-separators
  Bags/                  Seiferas bag-tree construction
  ZigZag/                zig-zag product, not used in main path
  Konig/                 König matching decomposition
  Misc/
Random/                  optional concrete expander certificates
docs/
scripts/
rust/
```

## Interfaces that look reusable

### `AKS/Halver/Defs.lean`

The repo defines the key interface approximately as:

```lean
structure HalverFamily (ε : ℚ) where
  depth : ℕ
  net : (m : ℕ) → ComparatorNetwork (2 * m)
  isHalver : ∀ m, IsEpsilonHalver (net m) ↑ε
  depth_le : ∀ m, (net m).depth ≤ depth
```

This is a natural target for a Paterson implementation if Paterson's local construction can be expressed as a uniform fixed-depth ε-halver family.

### `AKS/Halver/FromExpander.lean`

A `d`-regular graph with spectral gap at most `β` yields a `β`-halver. The computable König edge-coloring implementation has network depth at most `d`.

That is why the current enormous graph degree immediately becomes an enormous halver depth.

### `AKS/Separator/FromHalver.lean`

The current separator construction applies halvers at successive levels. The file proves that `t` levels cost at most

\[
t\cdot(\text{halver family depth}),
\]

and obtains separator error scaling with `t * ε` in the generic theorem.

This creates at least three quantitative attack surfaces:

1. lower halver depth;
2. a more efficient halver→separator conversion;
3. better bag parameters requiring weaker separator guarantees.

### `AKS/Bags/Params.lean`

The parameter structure includes:

- `γ`: separator fraction;
- `ε`: separator error;
- `ν`: capacity shrink factor per stage;
- `A`: capacity growth factor per tree level.

The file explicitly encodes conditions including

\[
(2\varepsilon A)^2<1,
\]

\[
\nu \ge 4\gamma A+\frac{5}{2A},
\]

\[
2A\varepsilon+\frac1A\le\nu,
\]

plus a separate `j = 1` master stranger constraint and finishing-capacity constraints.

Current concrete values:

\[
\gamma=\frac1{100},\qquad
\varepsilon=\frac1{100},\qquad
\nu=\frac{13}{20},\qquad
A=10.
\]

These are the same numerical parameters that independently surfaced in our Seiferas-based analysis.

### `AKS/Bags/Depth.lean`

The bag construction is parameterized before specialization. The conceptual split is:

```text
generic bag-tree correctness/depth theorem
    +
concrete Params + concrete separator/halver depth
    =
seiferasParams.depth
    =
top-level explicit constant
```

Current file proves:

```lean
theorem seiferasParams_depth_le :
  seiferasParams.depth ≤ 141 * 10 ^ 62
```

and also

```lean
theorem le_seiferasParams_depth :
  140 * 10 ^ 62 ≤ seiferasParams.depth
```

so merely tightening the final arithmetic inequality will not materially improve the constant. The local primitive and/or parameters must change.

## Build / trust notes

Recommended core build:

```bash
lake exe cache get
lake build AKS
```

Bare `lake build` also builds `Random/`, which may download very large certificate data.

The core `AKS/` proof is intended to stay within ordinary Lean/Mathlib trust. The optional `Random/` route has a larger engineering/trust footprint due to native evaluation and large external certificate data.

For an upstreamable improvement, preserving the core trust story is preferable.

## Repo-native improvement suggestions

The README itself lists:

- better spectral bound for MGG;
- fewer squarings;
- better Seiferas parameters;
- Paterson 1990 (`< 6100 log n`);
- much smaller historical Seiferas constants.

This aligns with our intended first contribution.

## What Codex should inspect locally

Grep for:

```text
seiferasParams
seiferasParams_depth_le
stagesFactor
HalverFamily
halverToSeparator
separator
depth
```

and trace the exact dependency graph from local primitive depth to the final numeral.

Use this document as a conceptual map, not as a substitute for inspecting the checked-out source.
