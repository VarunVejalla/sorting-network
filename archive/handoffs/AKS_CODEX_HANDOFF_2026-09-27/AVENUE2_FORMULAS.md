# Avenue-2 Mathematical Notes for Future Formalization

This file extracts the useful formulas without asserting the unproved global theorem.

## A. Global splitter cost

Assume a global construction with:

- base rank arity \(p\);
- splitter depth \(S(M)\);
- \(r\) sequential splitter passes per cycle;
- \(\gamma\) rank levels resolved per cycle;
- extra per-cycle binary depth \(B(M)\);
- cleanup/startup \(K(M)\).

Then

\[
D(n)
\le
(rS(M)+B(M))
\left\lceil\frac{\log_p n}{\gamma}\right\rceil
+
K(M).
\]

Normalize:

\[
\theta=\frac{\lg p}{\lg M},
\qquad
s=\frac{S(M)}{\lg M},
\qquad
b=\frac{B(M)}{\lg M}.
\]

Ignoring lower-order cleanup,

\[
\frac{D(n)}{\lg n}
\lesssim
\frac{rs+b}{\gamma\theta}.
\]

This formula is just depth accounting. The difficult part is proving the global scheduler/correctness theorem for any proposed splitter.

## B. Recursive splitter contraction

If

\[
S(M)
\le
\sum_j a_jS(M^{\alpha_j})
+b\lg M+o(\lg M),
\]

then after dividing by \(\lg M\),

\[
s(M)
\le
\sum_j a_j\alpha_j\,s(M^{\alpha_j})
+b+o(1).
\]

A sufficient normalized contraction condition is

\[
\sum_j a_j\alpha_j<1.
\]

This is the main reason to recurse a weaker splitter instead of the entire exact sorting theorem.

## C. Stronger condition for direct full-sort recursive calls

If the local gadget is implemented by recursive calls to the full sorting network rather than to a separately defined splitter, the global rank-progress factor matters.

Schematic direct recurrence:

\[
C(n)
\lesssim
\frac{1}{\gamma\theta}
\sum_j a_j\alpha_j C(M^{\alpha_j})
+
\text{local terms}.
\]

Then contraction requires roughly

\[
\sum_j a_j\alpha_j<\gamma\theta.
\]

This can be much stricter than merely `<1`.

## D. Why a `prepare once, use several times` primitive matters

The current memoryless global abstraction pays

\[
rS(M)
\]

because all Zig/Zag passes are sequential.

A stronger architecture of the form

\[
P(M)+rQ(M)
\]

would be significantly better if:

- `P` computes an expensive recursive partition/decomposition once;
- several later correction passes use that retained structure cheaply.

No such theorem has been proved yet, but this is one of the main structural ideas worth keeping in mind.

## E. Information-propagation lower bound for the safe fringe

The `GoodSplitter` geometry has roughly:

- \(p^2\) coarse rank bands;
- an extra factor \(p\) inside an outer fringe to identify a safe subfringe.

Thus the safe region is on a \(p^{-3}\) fraction of the local wires.

A depth-\(d\) binary comparator network gives any one output at most \(2^d\) possible ancestors. Covering all possible starting locations of an extreme element with a \(p^{-3}\)-fraction output region heuristically forces

\[
d\gtrsim3\lg p.
\]

This is a useful sanity lower bound: a `LocalFunnel` constant near 3 per \(\lg p\) would be close to the information-propagation floor.

## F. Current open truncated-Seiferas question

The full Seiferas process eventually makes fine rank cells exact.

We instead want to stop at time \(t\) while capacities are still large and show:

- the outer extreme fringe contains all but a \(\phi\) fraction of the relevant extreme cohort;
- the nested safe subfringe contains all but a \(\psi\) fraction of a smaller cohort;
- bulk misclassification normalized by one band is at most \(\eta\);

with

\[
q\asymp p^2,
\qquad
q\phi=O(1),
\qquad
\psi=O(1),
\qquad
\eta=O(1).
\]

The proof should use the already-formalized per-bag stranger invariant but avoid waiting until capacities fall below one.

A promising formal workflow would be:

1. identify which bags/subtrees correspond to coarse \(p^{-2}\)-scale bands;
2. sum the stranger tail crossing a coarse boundary;
3. separately sum the stranger tail crossing the nested \(p^{-3}\)-scale safe boundary;
4. express each leakage as a function of stage count \(t\);
5. solve for the smallest \(t=c\lg p\) meeting the three desired bounds;
6. compare \(c\) with the full-sort stage coefficient.

If \(c\) is strictly smaller, that would be the first concrete evidence of a true Avenue-2 advantage.
