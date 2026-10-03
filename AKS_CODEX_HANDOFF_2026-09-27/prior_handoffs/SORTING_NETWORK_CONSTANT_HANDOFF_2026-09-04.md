# Sorting-Network Asymptotic Depth Constant — Handoff
**Date:** 2026-09-04  
**Project goal:** Improve the best known upper bound on
\[
\limsup_{n\to\infty}\frac{D(n)}{\lg n},
\]
where \(D(n)\) is the minimum depth of an ordinary binary-comparator sorting network on \(n\) inputs and \(\lg=\log_2\).

---

## 1. Known asymptotic bounds / literature status

Let \(D(n)\) be ordinary binary comparator depth.

The best lower-bound constant discussed in this conversation is
\[
\liminf_{n\to\infty}\frac{D(n)}{\lg n}\ge 3.27\ldots
\]
(from Kahale–Leighton–Ma–Plaxton–Suel–Szemerédi; current-record lower bound as far as we checked).

For the upper bound:

- Paterson gives a conventional published explicit constant around \(6100\).
- Chvátal's 1992 technical report gives the stronger explicit theorem
  \[
  D(n)\le 1830\,\lg n-58657
  \]
  for all sufficiently large \(n\), hence
  \[
  \limsup_{n\to\infty}\frac{D(n)}{\lg n}\le 1830.
  \]
- Chvátal also reports a private/unpublished claim by Komlós of:
  - less than \(10\) in the analogous \(M\)-sorter normalization, and
  - roughly \(60\)–\(100\) for ordinary comparators.
  This is not an established published theorem.

### Where Chvátal's 1830 comes from

For \(N=64^d\), Chvátal uses:

- one special root separator: depth \(6320\),
- \(3d-21\) ordinary separator rounds: depth \(3660\) each,
- final \(2^{42}\)-sorter: depth \(903\).

Thus
\[
D(64^d)\le6320+(3d-21)3660+903
=10980d-69637
=1830\lg N-69637.
\]

Padding to the next power of \(64\) yields the \(-58657\) version for arbitrary large \(N\).

---

## 2. Important distinction: binary comparators vs. \(M\)-sorters

Define \(D_M(n)\) as the minimum depth of a sorting network where one primitive gate may exactly sort up to \(M\) inputs.

The main structural target developed in this conversation is **not**
\[
\limsup \frac{D(n)}{\lg n}\le24.
\]

The candidate structural theorem is instead
\[
D_M(n)\le (24+o_M(1))\log_M n+O_M(1).
\]

If an \(M\)-sorter is implemented by an ordinary comparator network of depth \(D(M)\), then
\[
D(n)\le D(M)\,D_M(n),
\]
hence
\[
\boxed{
\limsup_{n\to\infty}\frac{D(n)}{\lg n}
\le
(24+o_M(1))\frac{D(M)}{\lg M}.
}
\]

Thus \(24\) is an \(M\)-sorter coefficient, not yet the final binary constant.

With Batcher on \(M=2^L\),
\[
D(M)\le \frac{L(L+1)}2,
\]
so a structural coefficient \(24\) gives roughly
\[
12(L+1)
\]
as the binary constant, if the finite-parameter construction already works at that \(M\).

The ultimate program is therefore:

1. prove the structural \(24+o(1)\) theorem;
2. derive an explicit finite-\(M\) version with constants;
3. optimize \(M\) and the implementation depth \(D(M)\);
4. obtain an actual improved bound on
   \[
   \limsup D(n)/\lg n.
   \]

---

## 3. Chvátal's framework barrier

Chvátal's optimized \(M\)-sorter construction gives about
\[
24+16\sqrt2=46.627\ldots
\]
instead of \(48\), but his framework has an intrinsic lower barrier
\[
4(3+2\sqrt2)
=
12+8\sqrt2
=
23.313708\ldots.
\]

We independently rederived this barrier.

### Generic parent/fringe/children capacity obstruction

For a \(p\)-ary tree, with parent/child capacity ratio \(A\), time-shrinkage \(\nu\), and fringe fraction \(\lambda\), a parent receiving correction traffic from all \(p\) children gives
\[
\nu\gtrsim 2p\lambda A+\frac1{pA},
\]
so approximately
\[
\lambda\lesssim \frac{\nu}{pA}.
\]

Fresh first-order errors satisfy
\[
\mu\gtrsim\frac{\epsilon_B}{A\nu},
\]
while fitting those errors in the fringe requires
\[
\mu\lesssim\lambda.
\]

Therefore
\[
\epsilon_B\lesssim\frac{\nu^2}{p}.
\]

Writing
\[
p=M^\alpha,\quad A=p^a,\quad \nu=p^{-b},
\]
and using \(\epsilon_B=M^{-1/2+o(1)}\), optimization reproduces
\[
12+8\sqrt2.
\]

Conclusion: merely retuning Chvátal's parent/child kickback architecture cannot produce a major improvement. A direct/lateral Zig–Zag style architecture is required.

---

## 4. 1992 AKS "Halvers and Expanders" primitive

The 1992 AKS paper constructs depth-2 networks of large sorters with error
\[
\epsilon_B
=
\Theta\!\left(\sqrt{\frac{\log M}{M}}\right).
\]

The paper also indicates that one should split directly into many parts, roughly by first making on the order of \(p^2\) finer parts and combining them, rather than recursively building a multiway near-sorter from binary halvers.

This was the main clue motivating the current candidate construction.

---

## 5. Candidate new structural theorem

The current candidate theorem is:

> **Candidate theorem.**  
> For every \(\varepsilon>0\), for all sufficiently large sorter arities \(M\), there exists \(K_M\) such that for every \(n\),
> \[
> D_M(n)\le (24+\varepsilon)\log_M n+K_M.
> \]

Equivalently,
\[
\limsup_{n\to\infty}\frac{D_M(n)}{\log_M n}\le 24+o_M(1).
\]

### Intended parameterization

Use:

- \(p\)-ary rank tree,
- \(A=2p\),
- fine-part count
  \[
  q=2p^2,
  \]
- choose
  \[
  q\sim c\sqrt{\frac{M}{\log M}}
  \]
  for a sufficiently small fixed constant \(c>0\).

Then
\[
p
=
\Theta\!\left(
\left(\frac{M}{\log M}\right)^{1/4}
\right),
\]
so
\[
\log_M p=\frac14-o(1).
\]

One Zig–Zag–Zig cycle consists of three depth-2 \(M\)-sorter near-sorter passes, so cycle depth is \(6\).

If one cycle resolves one base-\(p\) rank level, the total depth is
\[
6\log_p n
=
(24+o(1))\log_M n.
\]

---

## 6. Why an earlier hoped-for \(12\) or \(8\) proof failed

An earlier simplification used only current-scale aligned/shifted equal windows. That was insufficient.

Reason: a key left a constant fraction of a coarse block away from its correct region after a coarse-scale cycle may never move far enough during all later, smaller-scale operations.

The genuine AKS Zig/Zag construction is multiscale: internal-tree registers at many levels remain active simultaneously, and alternating cherries revisit coarse mistakes.

Thus the project moved to a \(p\)-ary generalization of the genuine AKS multiscale register architecture.

---

## 7. \(p\)-ary register reassignment lemma — derived

Let \(N=p^d\). A level-\(i\) natural rank interval has length
\[
L_i=N/p^i.
\]

At time \(t\), define edge radius
\[
W_t(i)=\lambda Np^{-t}A^{i+1-t},
\]
with \(A=2p\) and \(\lambda>0\) sufficiently small.

Registers are assigned shallowest-first:

1. each level-\(i<t\) node claims still-unclaimed registers in its natural interval within distance \(W_t(i)\) of either endpoint;
2. remaining registers belong to level-\(t\) leaves.

Key scaling identities:
\[
W_{t+1}(i)=\frac{W_t(i)}{pA},
\]
\[
W_{t+1}(i+1)=\frac{W_t(i)}p,
\]
\[
W_{t+1}(i+2)=\frac ApW_t(i).
\]

With \(A\ge p\), any internal-node register descends by at most two levels.

### Safe subfringe

For a fresh edge component, the part within distance \(W_t(i)/p\) of the edge descends by at most one level.

For an inherited edge component
\[
\frac{W_t(i)}A<d\le W_t(i),
\]
the safe part is
\[
\frac{W_t(i)}A<d\le\frac{W_t(i)}p.
\]

Its relative size is
\[
s(A,p)=\frac{A-p}{p(A-1)}.
\]

For \(A=2p\),
\[
s(2p,p)=\frac1{2p-1},
\]
so one can reserve a safe fraction \(1/(2p)\) of every edge component.

### Wrongness consequence

If key wrongness is ancestor distance \(w\), then bookkeeping gives:

- arbitrary internal register:
  \[
  w^B\le w+2;
  \]
- safe register:
  \[
  w^B\le w+1;
  \]
- current bottom-level register:
  \[
  w^B\le w+1.
  \]

This is one of the major geometric components of the candidate proof.

---

## 8. Local depth-2 splitter with bulk + ordinary fringe + nested safe fringe

One \(p\)-ary cherry is represented as an \(m\times n\) matrix.

Use:
\[
m=(q+2)f,
\]
with:

- outer fringe \(F_-\): height \(f\),
- \(q=pA=2p^2\) fine bulk blocks: each height \(f\),
- outer fringe \(F_+\): height \(f\).

Inside each \(F_\pm\), reserve a safe subfringe of height
\[
s=\left\lfloor\frac{f}{2p}\right\rfloor.
\]

The same depth-2 random scramble should satisfy simultaneously:

1. **Bulk property \(B\)**:
   \[
   \epsilon_B
   \gtrsim
   \sqrt{\frac{2(1+\ln m)}m}.
   \]

2. **Ordinary fringe property \(F_f\)**:
   for sufficiently small extreme sets, all but \(\phi\) fraction land in the outer \(f\) rows.

3. **Nested safe-fringe property \(F_s\)**:
   for even smaller extreme sets, all but \(\psi\) fraction land in the outermost \(s\) rows.

The argument developed in this conversation strengthens Chvátal's Property-F probability constant and union-bounds over:

- bulk event,
- upper/lower ordinary fringe,
- upper/lower nested safe fringe.

Thus a single fixed scramble can satisfy all five required events.

### Asymptotic parameter sizes

With
\[
q\sim c\sqrt{\frac{M}{\ln M}},
\]
we get
\[
f\sim \frac1c\sqrt{M\ln M},
\]
and
\[
s
=
\Theta\!\left(
c^{-3/2}M^{1/4}(\ln M)^{3/4}
\right).
\]

Define fresh bulk error normalized by one fine block:
\[
\eta=(q+2)\epsilon_B.
\]
Then
\[
\eta=O(c).
\]

For ordinary fringe:
\[
\phi=O\left(\frac{\ln f}{f}\right),
\]
hence
\[
q\phi=O(c^2).
\]

For nested safe fringe:
\[
\psi=O\left(\frac{\ln s}{s}\right),
\]
and
\[
p\psi=O(c^2).
\]

Thus by taking \(c\) sufficiently small, all required local error constants can be made small while keeping the exponent
\[
\log_Mp=\frac14-o(1).
\]

---

## 9. Safe/rogue state split

The crucial invariant distinguishes far errors by spatial localization.

For wrongness \(r\ge2\):

- **safe**: key lies in the designated extreme safe subfringe pointing toward its correct ancestor;
- **rogue**: wrongness \(\ge2\), but not safely localized.

Normalize by fine-block size \(F\):

\[
G_r=
\sup_J
\frac{\#\{\text{safe keys in }J:w\ge r\}}F,
\]
\[
U_r=
\sup_J
\frac{\#\{\text{rogue keys in }J:w\ge r\}}F,
\]
\[
H_r=G_r+U_r.
\]

Let:

\[
\alpha:=6q\phi,
\]
\[
\beta:=6\psi,
\]
\[
\sigma:=6\phi\eta.
\]

The intended smallness conditions are
\[
\alpha\le\frac1{50},
\qquad
\beta\le\frac1{12}.
\]

---

## 10. Zig–Zag–Zig transition table

Bookkeeping plus three alternating cherry passes gives the following intended deterministic behavior for nonexceptional keys:

| Source | Bookkeeping | Two successful corrections | Result |
|---|---:|---:|---|
| near, \(w\le1\) | \(w\le3\) | \(w\le1\) | near |
| safe \(S_r\) | \(w\le r+1\) | \(w\le r-1\) | safe, lower wrongness |
| rogue \(R_r\) | \(w\le r+2\) | \(w\le r\) | safe at same/lower wrongness |
| safe \(S_{r+1}\) | \(w\le r+2\) | \(w\le r\) | contributes to \(S_r\) |

The key qualitative maps are:
\[
S_{r+1}\to S_r,
\]
\[
R_r\to S_r.
\]

Thus safe errors decrease in wrongness; rogue errors can fail to decrease for one cycle but should become safe.

---

## 11. Explicit safe/rogue recurrence derived

The explicit recurrence developed in the conversation is:

\[
G_2^+\le G_3+U_2+\sigma,
\]
\[
U_2^+\le \beta(G_3+U_2)+\sigma,
\]

\[
G_3^+\le G_4+U_3+\alpha H_2+\sigma,
\]
\[
U_3^+\le \beta(G_4+U_3)+\alpha H_2+\sigma,
\]

and for \(r\ge4\),
\[
\boxed{
G_r^+
\le
G_{r+1}+U_r+\alpha H_{r-1},
}
\]
\[
\boxed{
U_r^+
\le
\beta(G_{r+1}+U_r)+\alpha H_{r-1}.
}
\]

### Explicit invariant

Take
\[
\rho=\frac14,
\qquad
\kappa=\frac14,
\qquad
K=128.
\]

Claimed invariant:
\[
\boxed{
G_r\le128\sigma\,4^{-(r-2)},
}
\]
\[
\boxed{
U_r\le32\sigma\,4^{-(r-2)}.
}
\]

Under
\[
\alpha\le1/50,\qquad\beta\le1/12,
\]
the numerical recurrence closes with slack.

For example, the safe high-order multiplier is
\[
\rho+\kappa+\frac{\alpha(1+\kappa)}{\rho}
=
\frac12+5\alpha
\le0.6<1.
\]

The rogue multiplier is
\[
\beta(\rho+\kappa)+\frac{\alpha(1+\kappa)}{\rho}
=
\frac\beta2+5\alpha
<
\frac14.
\]

Low-order additive source \(\sigma\) is absorbed by \(K=128\).

Safe-fringe capacity also works because
\[
p\sigma\to0.
\]

---

## 12. What is proved vs. what remains conditional

### Strongly established / essentially proved in the conversation

1. Chvátal 1830 arithmetic.
2. Chvátal-framework \(23.3137\) barrier derivation.
3. \(p\)-ary edge-radius scaling and at-most-two-level reassignment.
4. Existence and size of a \(1/(2p)\)-scale safe subfringe for \(A=2p\).
5. Wrongness increment bounds:
   - arbitrary: \(+2\),
   - safe: \(+1\).
6. Numerical closure of the explicit safe/rogue recurrence once its transition inequalities are valid.
7. Asymptotic local splitter parameter scaling:
   \[
   p=\Theta((M/\log M)^{1/4}),
   \]
   \[
   \eta=O(c),
   \quad
   q\phi=O(c^2),
   \quad
   p\psi=O(c^2).
   \]
8. A plausible union-bound route showing one depth-2 scramble can satisfy bulk + ordinary fringe + nested fringe simultaneously.

### Still needs a rigorous global audit

The main remaining issue is **not** the numerical recurrence. It is the exact combinatorial interface between:

- \(p\)-ary register reassignment,
- Zig/Zag cherry parity,
- direct multiway splitter wiring,
- safe/rogue localization.

Specifically, a complete proof must rigorously verify that the local behavior really implies the transition inequalities above, including:

1. exact definition of each \(p\)-ary Zig and Zag cherry;
2. disjointness of all sorter gates in one pass;
3. exact parity behavior giving every far key at least two useful correction opportunities in Zig–Zag–Zig;
4. proof that a nonexceptional rogue far key becomes **safe** after those corrections;
5. proof that fresh near error contributes only the claimed \(\sigma\), rather than a hidden \(p\)- or \(q\)-factor;
6. proof that ordinary and nested Property F apply to the exact subsets generated dynamically;
7. root and bottom boundary cases;
8. integer rounding/divisibility;
9. arbitrary \(n\), not only \(p^d\);
10. final cleanup once wrongness \(\ge2\) disappears.

This audit is the next major task.

---

## 13. Suggested Lean formalization plan

Do **not** start by formalizing limsup.

Formalize the constructive theorem first.

### Layer A: generic network definitions

Define:

- binary comparator network;
- \(M\)-sorter network;
- depth;
- composition;
- parallel layer;
- sorting correctness;
- zero-one principle.

Prove:
\[
D(n)\le D(M)D_M(n).
\]

### Layer B: \(p\)-ary rank tree / bookkeeping

Define:

- natural interval of a node;
- ancestor;
- register owner;
- edge radius \(W_t(i)\);
- fresh/inherited edge components;
- safe subfringe;
- wrongness.

Prove the reassignment lemma as an independent theorem.

### Layer C: abstract local splitter contract

Define a structure such as:

```text
GoodSplitter
  (M p q f s : Nat)
  (eta phi psi : ℝ)
```

with fields encoding:

- bulk error,
- ordinary extreme fringe,
- nested safe fringe,
- depth \(=2\).

Prove the global Zig/Zag construction **assuming** `GoodSplitter`.

Separately prove probabilistic existence of `GoodSplitter`.

### Layer D: safe/rogue recurrence

Formalize \(G_r,U_r\).

Prove the six transition inequalities.

Then prove the numerical invariant:
\[
G_r\le128\sigma4^{-(r-2)},
\]
\[
U_r\le32\sigma4^{-(r-2)}.
\]

### Layer E: global theorem

Construct the full network for every \(n\), prove sorting, and prove
\[
\operatorname{depth}\le6\lceil\log_p n\rceil+O(1).
\]

Then choose
\[
p=\Theta((M/\log M)^{1/4})
\]
to derive
\[
D_M(n)\le(24+o_M(1))\log_M n+O_M(1).
\]

Finally derive the limsup statement and binary substitution corollary.

---

## 14. Recommended Lean theorem statement

The clean core theorem should be constructive, e.g. conceptually:

\[
\boxed{
\forall \varepsilon>0,\;
\exists M_0,\;
\forall M\ge M_0,\;
\exists K_M,\;
\forall n\ge2,\;
\exists \mathcal N,
}
\]

such that

\[
\operatorname{Sorts}(\mathcal N)
\]
and
\[
\operatorname{depth}(\mathcal N)
\le
(24+\varepsilon)\frac{\lg n}{\lg M}+K_M.
\]

Equivalently,
\[
D_M(n)
\le
(24+\varepsilon)\log_M n+K_M.
\]

The limsup theorem should be a corollary.

---

## 15. Final binary-comparator corollary to target eventually

Once the structural theorem is proved:

\[
\boxed{
\limsup_{n\to\infty}
\frac{D(n)}{\lg n}
\le
(24+\varepsilon)\frac{D(M)}{\lg M}
}
\]
for each sufficiently large finite \(M\) satisfying the explicit finite-parameter construction.

To get a genuine numerical improvement on 1830, the next phase after the structural proof is:

1. make all asymptotic inequalities explicit;
2. find the smallest/optimal workable \(M\);
3. plug in the best explicit binary depth \(D(M)\);
4. optimize
   \[
   C(M)=c_M\frac{D(M)}{\lg M}.
   \]

Do **not** confuse the structural coefficient \(24\) with the final binary constant.

---

## 16. Immediate next task for the fresh conversation

The next conversation should **not** redo the literature survey or rederive 1830.

Start here:

> Audit and formalize the global \(p\)-ary Zig–Zag–Zig theorem. In particular, define the exact \(p\)-ary cherry wiring and prove that bookkeeping + one Zig–Zag–Zig cycle implies the explicit safe/rogue transition recurrence:
> \[
> \begin{aligned}
> G_2^+&\le G_3+U_2+\sigma,\\
> U_2^+&\le\beta(G_3+U_2)+\sigma,\\
> G_3^+&\le G_4+U_3+\alpha H_2+\sigma,\\
> U_3^+&\le\beta(G_4+U_3)+\alpha H_2+\sigma,\\
> G_r^+&\le G_{r+1}+U_r+\alpha H_{r-1},\\
> U_r^+&\le\beta(G_{r+1}+U_r)+\alpha H_{r-1}\quad(r\ge4),
> \end{aligned}
> \]
> with no hidden \(p\)- or \(q\)-dependent losses.

If that audit succeeds, proceed directly to the full structural theorem
\[
D_M(n)\le(24+o_M(1))\log_M n+O_M(1),
\]
then only afterward optimize the binary constant.

---

## 17. Important caution for the fresh conversation

Several intermediate ideas in the exploration were explicitly rejected:

- **Rejected:** direct proof of binary limsup constant \(24\).
- **Rejected:** current-scale-only aligned/shifted windows giving \(12+o(1)\).
- **Rejected:** naive \(8+o(1)\) proof.
- **Rejected:** simply retuning Chvátal parent/fringe/child capacity parameters.
- **Rejected:** assuming ordinary halver prefix guarantees automatically give geometric displacement tails.

The current \(24\)-program arose only after accounting for:

- genuine multiscale AKS register storage,
- two-level physical reassignment,
- one-level safe reassignment,
- safe/rogue state splitting,
- nested fringe localization,
- direct \(p\)-ary multiway splitting.

Do not silently revert to the simpler invalid arguments.

---

## 18. Source papers / documents

See the companion `SORTING_NETWORK_SOURCES_2026-09-04.md` in the handoff package for URLs and why each source matters.
