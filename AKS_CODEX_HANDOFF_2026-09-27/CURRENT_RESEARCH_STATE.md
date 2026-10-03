# Current Research State

## 1. Ultimate mathematical objective

Let \(D(n)\) be the minimum depth of an ordinary sorting network on \(n\) inputs using binary comparators.

The project objective is to improve the explicit asymptotic upper constant

\[
\limsup_{n\to\infty}\frac{D(n)}{\lg n}.
\]

Known constructions prove \(D(n)=O(\log n)\), but the explicit constants vary wildly depending on how the AKS machinery is made constructive.

The `girving/aks` repository is valuable because it already formalizes a complete constructive \(O(\log n)\) sorting network in Lean. Its explicit constant is gigantic, but its modular architecture means a better local primitive can potentially improve the final theorem without rebuilding the entire proof.

---

## 2. Backbone papers we have been using

### Ajtai–Komlós–Szemerédi (1983), *An O(n log n) Sorting Network*

Role:
- original AKS construction;
- multiscale rank-tree/cherry viewpoint;
- wrongness and repeated correction intuition;
- alternating Zig/Zag style structure.

### Mike Paterson (1990), *Improved Sorting Networks with O(log N) Depth*

Role:
- major simplification/improvement of AKS;
- quantitatively much better local/global construction than the naive explicit expander route;
- repository README reports a `<6100 log n` depth bound;
- likely best near-term route to a dramatic formal constant improvement.

### V. Chvátal, *Lecture Notes on the New AKS Sorting Network*

Role:
- explicit constant bookkeeping;
- separator Properties B/F;
- explicit 1830-style construction;
- fixed-arity / large-sorter viewpoint;
- useful framework for understanding where constants enter and how local splitter quality affects the global coefficient.

### Joel Seiferas, *Sorting Networks of Logarithmic Depth, Further Simplified*

Role:
- clean bag-tree correctness proof;
- per-bag stranger invariant;
- explicit parameter inequalities;
- current `girving/aks` formalization follows this proof.

### Ajtai–Komlós–Szemerédi (1992), *Halvers and Expanders*

Role:
- strong halver constructions using large sorters;
- depth-2 large-sorter halvers;
- direct multiway partitioning idea;
- inspiration for replacing exact local sorting by a weaker local approximate splitter.

### Margulis / Gabber–Galil

Role in **the current repo**, not in our mathematical strategy:
- source of a simple explicit regular expander with a fully formal spectral bound;
- allows a clean trusted expander→halver construction;
- not believed to be essential for obtaining a good explicit sorting constant.

---

## 3. Avenue 1: fixed-arity large-sorter program

We previously studied a structural theorem for \(M\)-sorter networks.

Define \(D_M(n)\) as the minimum depth if one gate may exactly sort up to \(M\) inputs.

The old candidate target was roughly

\[
D_M(n)
\le
(24+o_M(1))\log_M n+O_M(1).
\]

### Old p-ary geometry

A representative parameterization used:

\[
A=2p,
\qquad
q=2p^2,
\]

with

\[
p=\Theta\!\left((M/\log M)^{1/4}\right),
\]

so

\[
\log_M p=\frac14-o(1).
\]

The local p-ary cherry was partitioned into:

- a lower fringe \(F_-\),
- \(q\) fine bulk bands,
- an upper fringe \(F_+\),

with a smaller safe subfringe inside each outer fringe of relative size about \(1/(2p)\).

A careful register-reassignment analysis gave:

- arbitrary internal state can become at most two rank-tree levels worse after bookkeeping;
- a specially localized “safe” state becomes at most one level worse.

The old safe/rogue recurrence numerically closed if the local splitter had sufficiently small bulk/fringe errors.

### Why the old 24 theorem was not accepted

The numerical recurrence was not the main problem. The problem was the exact global interface:

- exact Zig/Zag cherry covers;
- pass disjointness;
- guaranteed number of useful correction opportunities;
- safe/rogue localization after a pass;
- fresh error accounting with no hidden \(p\) or \(q\) factor;
- dynamic extreme subsets satisfying the local splitter hypotheses;
- root/bottom boundary handling.

Subsequent auditing found hidden scale losses. A four-pass repair appeared to move the structural coefficient toward roughly \(40+o_M(1)\), but that is still provisional.

Therefore **do not formalize the old 24 theorem as if it were established.**

---

## 4. Avenue 2: recurse the weakest local primitive, not exact sorters

The central insight was that exact-sorter recursion is generally noncontractive.

If a fixed-arity theorem costs a structural coefficient \(c(M)>1\), and an \(M\)-sorter is recursively replaced by a binary sorting network, one gets schematically

\[
C(n)
:=
\frac{D(n)}{\lg n}
\lesssim
c(M)C(M).
\]

For a growing choice such as \(M=\lg n\), this can iterate to something like

\[
c^{\log^*n},
\]

which does not give a bounded asymptotic constant.

So Avenue 2 asks:

> What is the weakest local approximate splitter sufficient for the global proof, and can *that* be implemented recursively or directly in \(O(\lg M)\) binary depth with a contractive normalized recurrence?

---

## 5. `GoodSplitter` abstraction

We introduced a local gadget roughly of the form

\[
\operatorname{GoodSplitter}(M,p,q,f,s;\eta,\phi,\psi).
\]

The output layout is

\[
F_-, B_1,\ldots,B_q,F_+,
\]

where all coarse bands have size \(f\), and each outer fringe has a directional safe subfringe \(S_\pm\) of size \(s\).

The intended guarantees are:

1. **bulk correction** with normalized fresh exception \(\eta\);
2. **ordinary extreme-fringe guarantee**: every dynamically generated eligible extreme subset is sent to the correct outer fringe except for a \(\phi\) fraction;
3. **nested safe-fringe guarantee**: smaller extreme subsets are sent into the designated safe subfringe except for a \(\psi\) fraction;
4. both directions simultaneously;
5. bounded binary depth \(S(M)\).

Crucially, the local interface should **not** include:

- Zig/Zag parity;
- global wrongness definitions;
- rank-register reassignment;
- global “two useful corrections” statements.

Those belong to the scheduler/bookkeeping layer.

The intended composition is

\[
\text{bookkeeping geometry}
+
\text{scheduler}
+
\text{GoodSplitter}
\Longrightarrow
\text{global recurrence}.
\]

---

## 6. Global depth formula in terms of `GoodSplitter`

Let:

- \(S(M)\): binary depth of one whole splitter pass;
- \(r(M)\): number of sequential splitter passes per global cycle;
- \(\gamma(M)\): base-\(p\) rank levels resolved per cycle;
- \(B(M)\): extra binary depth per cycle outside splitters;
- \(K(M)\): startup/boundary/cleanup depth.

Then

\[
D(n)
\le
\left(r(M)S(M)+B(M)\right)
\left\lceil\frac{\log_p n}{\gamma(M)}\right\rceil
+
K(M).
\]

With

\[
\theta(M)=\frac{\lg p}{\lg M},
\quad
s(M)=\frac{S(M)}{\lg M},
\quad
b(M)=\frac{B(M)}{\lg M},
\]

this gives

\[
\frac{D(n)}{\lg n}
\lesssim
\frac{r\,s+b}{\gamma\theta},
\]

provided

\[
K(M(n))=o(\lg n)
\]

for a growing-arity schedule.

### Sharing audit

Within one pass, disjoint cherries run in parallel, so the cost is \(S(M)\), not number-of-cherries times \(S(M)\).

Across Zig/Zag passes, the passes act on changed wire values and different cherry covers; simply reusing the same *template* does not save depth.

Therefore under the current memoryless abstraction,

\[
\text{cycle cost}=rS(M)+B(M).
\]

A stronger “prepare once, use several times” interface remains an attractive research direction.

---

## 7. Recursive splitter fixed point

If one could construct

\[
S(M)
\le
\sum_j a_jS(M^{\alpha_j})
+b\lg M
+o(\lg M),
\]

and write

\[
s(M)=S(M)/\lg M,
\]

then

\[
s(M)
\le
\sum_j a_j\alpha_j s(M^{\alpha_j})
+b+o(1).
\]

Let

\[
A_*=\sum_j a_j\alpha_j.
\]

If

\[
A_*<1,
\]

the recurrence is contractive and suggests

\[
\limsup s(M)\le\frac{b}{1-A_*}.
\]

This is the core Avenue-2 fixed-point criterion.

There is a stricter condition if the recursive calls are not to the splitter \(S\) but to the *full sorting depth* \(D\). In that case the global factor \(1/(\gamma\theta)\) also enters the contraction coefficient.

---

## 8. Why the obvious recursive replacement failed

The old local depth-2 large-sorter construction had the structure:

```text
exact column sort
→ scramble
→ exact column sort
```

A tempting idea was to replace each exact sort by a recursive weak splitter.

This fails because the first exact sort does more than approximately partition: it **canonicalizes** each column.

For zero-one inputs, an exactly sorted column is determined only by its number of ones, giving polynomially many canonical possibilities. The probabilistic scramble proof can union-bound over those states.

If the recursive primitive leaves \(\delta m\) arbitrary mistakes in a column of height \(m\), the number of possible states becomes on the order of

\[
\exp(mH(\delta)),
\]

which destroys the same union bound unless \(\delta\) is essentially \(O(1/m)\), i.e. the recursive primitive is almost exact anyway.

Therefore the old sort→scramble→sort proof is not composable with a weak `GoodSplitter`.

---

## 9. Direct `LocalFunnel` attempt and what it taught us

We next tried to build the needed fringe behavior directly from binary halvers and repeated multiscale corrections.

### First failed simplification

We proposed a very simple global tail recurrence

\[
E_r^+
\le
E_{r+1}+\delta E_{r-1}.
\]

Auditing the rank-tree bookkeeping showed this was too optimistic.

An arbitrary state can incur +2 levels of bookkeeping wrongness. Three alternating Zig–Zag–Zig correction passes do not guarantee a strict net decrease in every phase alignment, even if the local separator never fails.

This is one reason a four-pass repair appears naturally.

### Second failed simplification

We tried amplifying a local separator by repeatedly filtering the residual extreme cohort. This can make the *old* extreme cohort error geometrically small.

However, that does not control **fresh first-order strangers** created because innocent filler elements are displaced into the wrong sibling.

An ordinary extreme-set separator alone is therefore insufficient.

---

## 10. Seiferas invariant closes the fresh-error issue

The correct machinery is the per-bag stranger invariant used by Seiferas and already formalized in `girving/aks`.

A representative form is

\[
N_j(B)
\le
\gamma\,\varepsilon^{j-1}\,\operatorname{capacity}(B),
\qquad j\ge1.
\]

The exact repo parameter constraints include:

\[
(2\varepsilon A)^2<1,
\]

\[
\nu\ge4\gamma A+\frac{5}{2A},
\]

\[
2A\varepsilon+\frac1A\le\nu,
\]

and a separate `j=1` master constraint that accounts for:

- inherited higher-order strangers;
- separator failures;
- ordinary halving error;
- ancestor/subtree imbalance;
- parity/capacity corrections.

The current Lean repo formalizes this. This is therefore a much safer foundation than our ad hoc tail recurrences.

---

## 11. Truncating Seiferas: exact classification is too strong

We derived the following conceptual consequence.

Suppose the bag-tree process is run until the nominal capacity just above a target rank depth falls below one. Because bag occupancies are integral and the per-bag strange-item tail is geometrically summable, the target-depth subtrees can become **exactly** rank-pure.

For the `GoodSplitter` geometry one can set approximately:

- coarse depth \(\sim2\lg p\), giving \(p^2\)-scale rank blocks;
- fine depth \(\sim3\lg p\), giving an additional factor-\(p\) subdivision suitable for the safe fringe.

If the process is run until exact rank purity at the fine depth, then the splitter errors become

\[
\eta=\phi=\psi=0.
\]

That sounds excellent, but it is the wrong stopping condition.

Why? Because exact classification into \(p^3\)-scale rank cells is already most of an exact sort. Sorting the tiny cells afterward costs only lower-order depth. Thus this “LocalFunnel” is effectively an exact sorter in disguise, and the construction collapses back to ordinary Seiferas/AKS sorting rather than producing a new contractive Avenue-2 primitive.

### Current genuine frontier

The interesting open problem is:

> stop the Seiferas/Paterson-style multiscale process **strictly before exact rank classification**, and prove only the weaker `GoodSplitter` guarantees:
>
> \[
> \eta=O(1),\qquad
> q\phi=O(1),\qquad
> \psi=O(1),
> \]
>
> with \(q\asymp p^2\), safe-fringe scale about \(1/p\) inside the outer fringe, and binary depth whose normalized coefficient is strictly better than full sorting.

This is where new mathematics could produce a true Avenue-2 contraction.

---

## 12. Why the `girving/aks` repository is a strong base

The repo already formalizes:

- comparator networks;
- zero-one principle;
- graph machinery;
- expander→halver;
- halver families;
- halver→separator;
- Seiferas parameters;
- bag capacities/fringes;
- stranger bounds;
- stage count/depth;
- arbitrary-\(n\) top-level sorting theorem;
- trusted-code audit.

Therefore there is little reason to rebuild the formal infrastructure from scratch.

The practical strategy should be:

### Conservative contribution first

Replace or improve the local primitive:

```text
current MGG^64-degree halver
    ↓
better halver / Paterson construction
```

while reusing `Separator/` and `Bags/`.

### Research contribution later

Once the known construction is formalized with a reasonable constant, consider extending the repo with a weaker splitter abstraction and a truncated bag-tree theorem implementing Avenue 2.

This ordering gives an immediate useful upstream contribution even if the novel research path takes much longer.
