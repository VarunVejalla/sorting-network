# Sorting Networks — Avenue 2 Recursive / Growing-Arity Handoff
**Date:** 2026-09-04  
**Purpose:** Start a separate line of attack aimed **directly** at improving the binary-comparator asymptotic depth constant
\[
\boxed{\limsup_{n\to\infty}\frac{D(n)}{\lg n}},
\]
where \(D(n)\) is the minimum depth of an ordinary sorting network on \(n\) wires using only binary comparators.

This handoff is intentionally focused on **Avenue 2**: allowing intermediate sorter arities to grow with \(n\), and/or recursively implementing the local primitives, instead of fixing one finite \(M\) and substituting a binary \(M\)-sorter once.

---

## 1. Primary objective

The only ultimate objective is a better constant \(C\) such that
\[
D(n)\le (C+o(1))\lg n.
\]
Equivalently,
\[
\limsup_{n\to\infty}\frac{D(n)}{\lg n}\le C.
\]

Any theorem stated in terms of \(M\)-sorters, multiway splitters, rank trees, halvers, etc. is **intermediate machinery only**.

The current best explicit upper benchmark in the project is Chvátal's
\[
\limsup D(n)/\lg n\le 1830.
\]
The project goal is to reduce this substantially, ideally to the low hundreds or better.

---

## 2. Avenue 1 vs. Avenue 2

### Avenue 1 — fixed finite \(M\), one-level substitution

Suppose we prove, for fixed sorter arity \(M\),
\[
D_M(n)\le c_M\log_M n+O_M(1),
\]
where one primitive gate may sort up to \(M\) inputs exactly.

Replacing each \(M\)-sorter by a binary sorting network of depth \(D(M)\) gives
\[
D(n)\le D(M)D_M(n),
\]
hence
\[
\boxed{
\limsup_{n\to\infty}\frac{D(n)}{\lg n}
\le
c_M\frac{D(M)}{\lg M}.
}
\]

Avenue 1 therefore seeks a finite \(M\) minimizing
\[
C(M)=c_M\frac{D(M)}{\lg M}.
\]

That work is continuing in the original conversation.

### Avenue 2 — growing arity / true recursion

Here we ask whether \(M\) should itself grow with \(n\), e.g. \(M=\lg n\), \(n^\alpha\), or according to a hierarchy \(M_0<M_1<\cdots<n\), while local primitives are recursively realized by smaller primitives.

The goal is **not** an asymptotic theorem in \(M\) for its own sake. The goal is to exploit recursive structure to improve the final binary constant.

---

## 3. The first obstruction: naive recursive exact-sorter substitution does not contract

Suppose a structural theorem has
\[
D_M(n)\le c(M)\log_M n+O_M(1),
\]
with \(c(M)\to c>1\) (the current candidate Avenue-1 architecture is provisionally around \(c\approx40\), not yet proved).

If every \(M\)-sorter is recursively implemented by an optimal binary network of depth \(D(M)\), then
\[
D(n)\lesssim c(M)\frac{\lg n}{\lg M}D(M).
\]
Define
\[
C(x):=\frac{D(x)}{\lg x}.
\]
Then the recurrence is essentially
\[
\boxed{C(n)\lesssim c(M)C(M).}
\]

If, for example, \(M=\lg n\) and \(c(M)\to40\), then
\[
C(n)\lesssim40C(\lg n).
\]
Iterating gives roughly
\[
C(n)\lesssim40^{\log^*n}C(O(1)),
\]
which diverges.

**Conclusion:** simply taking a fixed-\(M\) structural theorem with coefficient \(c>1\) and recursively substituting exact sorters at each scale does not preserve an \(O(\lg n)\) bound with a fixed constant.

This is the central obstruction Avenue 2 must overcome.

---

## 4. What kind of recurrence would actually help?

We want a recurrence whose normalized binary constant is **contractive**.

A model example is
\[
D(n)\le a\,D(n^\alpha)+b\lg n+o(\lg n).
\]
If
\[
D(n)\sim C\lg n,
\]
then
\[
C\le a\alpha C+b.
\]
Therefore, if
\[
\boxed{a\alpha<1,}
\]
we get
\[
\boxed{C\le\frac{b}{1-a\alpha}.}
\]

More generally, a recurrence
\[
D(n)\le\sum_j a_jD(n^{\alpha_j})+b\lg n+o(\lg n)
\]
would give
\[
C\le\left(\sum_ja_j\alpha_j\right)C+b,
\]
so the key condition is
\[
\boxed{\sum_ja_j\alpha_j<1.}
\]

This is a clean mathematical target for Avenue 2.

---

## 5. Why recursive use of **exact sorters** may be the wrong abstraction

The current AKS-style constructions do not actually need every local primitive to perform a complete exact sort on its input block. They typically need only properties such as:

- bulk multiway partitioning / halving;
- sending almost all sufficiently extreme keys into designated fringes;
- nested localization into a smaller safe fringe;
- limited rank-displacement error;
- deterministic correction opportunities under Zig/Zag cherry passes.

Thus implementing each local \(M\)-sorter by a full depth-\(D(M)\) binary sorter may be massive overkill.

A potentially stronger recursive program is:

> Recursively implement the **local splitter contract itself**, not an exact \(M\)-sorter.

For example, instead of paying \(D(M)\) to exactly sort a block of size \(M\), construct a binary network on those \(M\) wires of depth
\[
a\lg M+o(\lg M)
\]
that satisfies only the bulk/fringe/nested-fringe guarantees required by the global proof.

If \(a\) is small enough, the global coefficient might be competitive even when the abstract \(M\)-sorter coefficient is large.

This is likely one of the most promising Avenue-2 directions.

---

## 6. Current Avenue-1 architecture that may be recursively exploited

The current structural program is a \(p\)-ary generalization of genuine AKS Zig/Zag multiscale register bookkeeping:

- a \(p\)-ary rank tree;
- multiscale edge registers retained across time;
- alternating Zig/Zag cherries;
- a depth-2 multiway near-sorter/splitter primitive;
- safe/rogue far-error localization;
- ordinary and nested safe fringes;
- direct correction of coarse rank mistakes at multiple scales.

The earlier \(24+o_M(1)\) candidate was found to have hidden scale losses during the exact global-transition audit. The current provisional repair suggests a structural coefficient around \(40+o_M(1)\) with four alternating passes, but **this is not yet a proved theorem**.

Avenue 2 should not depend strongly on whether the final Avenue-1 structural coefficient is 40, 42, or somewhat different. Its key question is whether the **binary realization of the local primitives can be recursively shared/contracted** rather than paying a full exact-sorter cost at every level.

---

## 7. Concrete Avenue-2 research questions

### A. Recursive splitter realization

Define the weakest local primitive sufficient for the global Zig/Zag proof. Ideally a structure such as

```text
GoodSplitter(M, p, q, f, s; eta, phi, psi)
```

with guarantees for:

1. bulk error \(\eta\);
2. ordinary fringe error \(\phi\);
3. nested safe-fringe error \(\psi\);
4. exact wire capacity / displacement geometry;
5. bounded binary depth.

Then ask:

\[
\boxed{\text{What is the minimum binary depth needed for GoodSplitter on }M\text{ wires?}}
\]

Do not require exact sorting unless the proof truly needs it.

### B. Can `GoodSplitter` be built self-similarly?

Try to derive a recurrence of the form
\[
S(M)\le\sum_j a_jS(M^{\alpha_j})+b\lg M+o(\lg M),
\]
where \(S(M)\) is the binary depth needed for the splitter contract, and where
\[
\sum_ja_j\alpha_j<1.
\]

If so, \(S(M)=O(\lg M)\) with an explicit fixed-point constant.

### C. Avoid paying recursive cost on every global pass

The naive recurrence multiplies the recursive cost by the full structural coefficient because every abstract sorter layer is independently replaced by a recursive exact sorter.

Look for architectures in which:

- only some passes require expensive recursive splitting;
- other passes are cheap binary routing/matching layers;
- a recursively produced partition can be **reused across several correction passes**;
- multiple cherries share one lower-level decomposition;
- one recursive splitter call services several subsequent global layers.

This could turn the normalized recurrence from
\[
C(n)\le cC(M)
\]
into something contractive.

### D. Variable arity by level/time

Instead of a single \(M\), choose \(M_i\) depending on rank-tree level or time. Analyze total depth as
\[
\sum_i \text{cost}(M_i)
\]
subject to the amount of rank progress achieved at each scale.

The optimization target should be the ratio
\[
\frac{\text{binary depth spent}}{\text{bits of rank scale resolved}}.
\]

This is more fundamental than minimizing an \(M\)-sorter coefficient in isolation.

### E. Direct binary implementation of depth-2 large-sorter halvers

The AKS 1992 *Halvers and Expanders* construction gets very strong error from depth-2 networks of **large sorters**. Investigate whether those two large-sorter layers can themselves be replaced by structured binary networks more efficiently than full sorting.

Possible ingredients:

- expander/halver networks;
- sparse compare-exchange layers;
- recursive approximate partitioners;
- randomized/probabilistic existence followed by fixing one network;
- compositions that preserve Property-F-type extreme-set guarantees.

The relevant cost is the binary depth required to achieve the needed **error exponents**, not to fully sort each local block.

### F. Fixed-point formulation

Try to formulate the entire architecture as an operator on achievable constants.

For example, if binary networks with normalized depth constant \(C\) can be used as subroutines to produce a larger network with constant
\[
F(C),
\]
then seek
\[
F(C)<C
\]
for some starting \(C\), or a fixed point
\[
C_*=F(C_*)
\]
with \(C_*\) far below existing explicit bounds.

This may be a cleaner way to reason about recursive variable-arity constructions than choosing \(M(n)\) ad hoc.

---

## 8. A useful optimization abstraction

Suppose a local recursive primitive of scale \(m\) costs
\[
S(m)=(a+o(1))\lg m.
\]
Suppose one global cycle costs \(r\) calls to that primitive and resolves \(\gamma\lg m\) bits of rank scale.

Then the contribution to the final normalized binary depth is roughly
\[
\boxed{\frac{ra}{\gamma}.}
\]

Avenue 2 should continuously optimize this **cost per resolved rank bit**, rather than separately optimizing an abstract sorter coefficient and an implementation coefficient.

This viewpoint may reveal ways to share or amortize recursive work that are invisible in the product
\[
c_M\frac{D(M)}{\lg M}.
\]

---

## 9. Immediate recommended task for the new conversation

Do **not** begin by optimizing a particular choice such as \(M=\lg n\). First determine what recursive recurrence is structurally possible.

Recommended first task:

> **Abstract the current global Zig/Zag proof so its local primitive is the weakest possible approximate splitter rather than an exact \(M\)-sorter. Then derive the binary-depth recurrence obtained if that splitter is itself built recursively. Identify exactly which recursive calls are duplicated across passes and which can be shared. Determine whether the resulting normalized recurrence is contractive.**

Concretely:

1. Write an abstract `GoodSplitter` contract containing only the properties actually used globally.
2. Let \(S(M)\) denote minimum binary depth realizing that contract.
3. Express total binary depth of the \(n\)-wire global construction directly in terms of \(S(M)\), **without introducing exact \(M\)-sorters unless necessary**.
4. Allow \(M=M(n)\) and recursively upper-bound \(S(M)\).
5. Derive the induced recurrence for
   \[
   C(n)=D(n)/\lg n.
   \]
6. Look specifically for a contraction coefficient \(<1\).
7. Only after that, optimize the arity schedule and numerical constants.

If the induced recurrence is still of the form
\[
C(n)\geq/\lesssim cC(M)+O(1)
\]
with \(c>1\), identify which repeated local operations cause the multiplicative factor and redesign those operations.

---

## 10. Things not to assume

1. **Do not assume \(M=\lg n\) is automatically useful.** Under naive exact-sorter substitution it leads to a divergent \(c^{\log^*n}\) normalized factor when \(c>1\).

2. **Do not require exact sorting locally unless needed.** Approximate partition/splitter guarantees are likely enough.

3. **Do not confuse an \(M\)-sorter coefficient with the desired binary constant.** The only target is \(D(n)/\lg n\).

4. **Do not treat the provisional Avenue-1 coefficient 40 as established.** Its global proof is still being audited.

5. **Do not recurse the same black-box theorem blindly.** True progress requires a recurrence that is contractive after normalization.

---

## 11. Relevant literature / files

The companion source list in this package gives URLs and context:

- V. Chvátal, *Lecture Notes on the New AKS Sorting Network* — explicit 1830 binary constant; separator framework; Properties B/F; historical constants.
- Ajtai–Komlós–Szemerédi, *An O(n log n) Sorting Network* — genuine multiscale Zig/Zag/cherry architecture.
- Ajtai–Komlós–Szemerédi, *Halvers and Expanders* — depth-2 large-sorter halvers and direct multiway partitioning ideas.
- Seiferas, *Sorting Networks of Logarithmic Depth, Further Simplified* — historical simplifications and error recurrences.

See `SORTING_NETWORK_SOURCES_2026-09-04.md`.

---

## 12. Success criterion for Avenue 2

The ideal outcome is **not** merely another theorem of the form
\[
D_M(n)\le c\log_Mn.
\]

The ideal outcome is a direct recursive binary theorem, for example
\[
D(n)\le C\lg n+o(\lg n)
\]
with an explicit improved constant \(C\), obtained from a provably contractive multiscale recurrence.

A strong intermediate result would be an abstract theorem saying:

> If a splitter contract of scale \(m\) is available with binary depth \((a+o(1))\lg m\), then the global construction has binary depth \((F(a)+o(1))\lg n\), where \(F\) is explicit.

Then the recursive problem becomes the fixed-point optimization
\[
C\le F(C).
\]

That is the central Avenue-2 program.
