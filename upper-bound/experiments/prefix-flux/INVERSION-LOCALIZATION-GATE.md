# Inversion potential as a localization gate

2026-10-21. Codex (GPT-6). Exact combinatorial lemmas and a conditional
depth calculation; no new sorting bound is claimed.

## Exact link to prefix flux

Let `w` be a Boolean word of length `N` with `q` zeros. Write `Z(r)` for the
number of zeros in positions `[0,r)`, and define the prefix defect

```text
F(r) = min(q,r) - Z(r),   0 <= r <= N.
```

Then

```text
sum_{r=0}^{N-1} F(r) = inv(w),
```

where `inv(w)` is the number of pairs `i<j` with `w[i]=1,w[j]=0`.
Indeed, if the zero positions are `z_0<...<z_{q-1}`, then zero `z_k` has
exactly `z_k-k` preceding ones, so `inv(w)=sum_k(z_k-k)`. Also
`sum_r Z(r)=sum_k(N-1-z_k)`, and subtracting this from
`sum_r min(q,r)` gives the same expression. Thus the pointwise global
prefix-flux state already tracked in `PROFILE-GATE.md` has an exact aggregate
potential interpretation.

This does not show that the D2 stage contracts `inv`; prefix dominance only
shows it is nonincreasing.

## Small inversion count localizes every error

Every misplaced one at position `p<q` contributes at least `q-p` inversions:
there are at least `q-p` zeros after it. Every misplaced zero at `p>=q`
contributes at least `p-q` inversions from preceding ones. Consequently, if
`inv(w)<=I`, all wrong bits lie in the interval

```text
[max(0,q-I), min(N,q+I+1)),
```

of length at most `2I+1`. Outside it, the word is exactly `0*1*`. This gives
a positional localization contract from an aggregate potential; it is
stronger than merely bounding the number of wrong bits.

## Fixed cleanup and the coefficient gate

Suppose a fixed prefix network `P_n` has depth
`p*log2(n)+O(1)` and, on every Boolean input, leaves inversion count at most
`n^theta`. By the preceding lemma this leaves a contiguous dirty interval of
length at most `2*n^theta+1`, with zeros before it and ones after it. The
interval may depend on the input; the network may not.

The interval can be cleaned by a fixed recursive schedule. Let `B` be the
next power of two at least `2*n^theta+1`. For large `n`, partition into
`2B` chunks; if the final remainder is shorter than `B`, join it to the
previous chunk. Thus every chunk has length at least `B`, and every chunk
with two neighbors has length at least `2B`. Recursively sort every chunk in
parallel, then merge the suffix and prefix halves across each chunk boundary.
The seam windows are disjoint and each merge costs `log2(2B)+O(1)`. If the
dirty interval lies in one chunk, sorting that chunk fixes it. If it crosses
a boundary, its at most `B` bits imply that after chunk sorting all ones in
the left chunk and zeros in the right chunk lie in the seam halves; the seam
merge fixes them. Sorted surrounding portions remain in order. Bounded small
`n` cases are handled exactly as base cases.

If `F(n)` is the resulting exact sorting depth, this gives

```text
F(n) <= p*log2(n) + F(4*n^theta+O(1)) + theta*log2(n) + O(1),
limsup F(n)/log2(n) <= (p+theta)/(1-theta).
```

For the baseline UB-42 prefix budget `p=292.5`, reaching at most300 requires

```text
theta <= (300-292.5)/301 = 15/602 ~= 0.0249169.
```

Strictly below300 requires strict inequality (or some slack in `p`). This is
a concrete new terminal gate for UB-42: prove the actual priced prefix
schedule drives the global inversion count below `n^theta` for some
`theta<15/602`, then use the fixed cleanup above. The current rank-profile
tests do not establish such a bound; the exact root, provider, and all-depth
contraction remain open. If the prefix stage only gives a looser inversion
exponent, the displayed budget rejects this cleanup route at `p=292.5`.

The parameter screen has a more favorable but still conditional `(3,3,2)`
candidate: row height `2^13`, three-sort depth273, stage rate1, hence
`p=273`. Its cleanup gate is

```text
theta <= (300-273)/301 = 27/301 ~= 0.089701.
```

This gives substantially more room and is the better UB-42 parameter target
if the new row-height-13 provider and all-depth flow bounds can be proved.
The depth-30 fringe ratio and the sparse adversary runs below are finite
screens only; they do not establish either prerequisite.

## Finite ordered inversion screen

`sparse_probe.py` now accepts D2 parameters and row height and reports the
exact inversion count of its interval-encoded trace without expanding the
ambient word. The interval formula was exhaustively checked against all
Boolean words through length11. It asserts inversion nonincrease at every
oracle stage and prints a compact summary by default (`--verbose` retains the
full histories).

For `(3,3,2)`, row height8192, scale8192, threshold1/3, root error fraction
`10^-7`, and the assumed rank-tail oracle, the initial-band trace gives:

| flow depth | ambient `N` | final inversions | `log_N(inv)` | remaining wrong bits |
|---:|---:|---:|---:|---:|
| 12 | `2^49` | 46,225 | 0.3163 | 430 |
| 20 | `2^73` | 1,669,264 | 0.2832 | 2,584 |
| 24 | `2^85` | 3,845,521 | 0.2573 | 3,922 |

Each trace has zero wrong bits in every noncrossing terminal native block;
the displayed errors lie in the threshold-crossing block. At depth12, outer
and left-end initial bands also reached that terminal condition, with final
inversion counts834,415 and293,690 respectively. The three depth-specific
exponents trend downward but are far above `27/301`; the final counts are
small relative to `N`, not yet a certified power law. The oracle selects
input-dependent port outputs under assumed local tails, so these traces are
discovery evidence only and do not prove a fixed provider or a uniform
inversion bound.
