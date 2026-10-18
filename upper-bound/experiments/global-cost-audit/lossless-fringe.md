# Lossless fringe capture: correction and a cyclic construction

Informal mathematical derivation, 2026-10-10. No Lean theorem or improved
global bound is claimed.

## Correction to the preceding investigation

The existing small-rank proposal is stronger than a sparse arbitrary-column
promise. After the intermediate column sort, it assumes

```
E_g(z) = sum_c max(z_c-g,0) < eta*j,
g + eta*j <= f.
```

Therefore every height `z_c<=f`. Since those columns are sorted, all high
marks are already in the bottom `f` rows. A row scramble preserves the row
of each key, so they remain there before any final repair. The symmetric
statement holds for low keys in the top `f` rows. Subsequent ascending
comparators preserve both guarantees.

Thus **this premise does not require a sparse compactor at all**. The previous
candidate audit mistakenly treated `z_c<=f` as if the second scramble could
move those marks to arbitrary rows. It cannot. An arbitrary sparse-compaction
problem would arise only from a different, weaker promise on the pre-repair
column counts. The outstanding question here is existence of the stronger
first-round premise together with bulk control and a common witness.

## A deterministic small-rank construction

There is an alternative that supplies lossless small-rank capture directly.
Sort each input column, apply the cyclic row scramble

```
sigma_r(c) = c+r mod n,
```

then sort the columns again. Fix one destination column. Measured from the
bottom, its source column cycles through all `n` columns with period `n`.
The same property holds when measured from the top.

For `k` high marks reaching that destination, choose their distinct row
heights `t>=1`. If `a_c` chosen heights use source column `c`, its original
sorted height must be at least the largest of those heights. Its first
possible height is a distinct residue representative `r_c` in `{1,...,n}`;
its largest chosen height is at least `r_c+n*(a_c-1)`.

If `d` source columns are used, the total number `j` of input marks satisfies

```
j >= n*(k-d) + d*(d+1)/2,
1 <= d <= min(k,n).
```

The right side is minimized at `d=min(k,n)` (the adjacent difference is
`d+1-n`). Hence

```
j >= M_n(k),
M_n(k) = k*(k+1)/2                  if k<=n,
         n*k - n*(n-1)/2            if k>=n.
```

This argument counts actual input mass, not independent demands, and applies
to every sorted input profile for the same deterministic scramble. It proves
that the second column sort has height at most `f` whenever `j<M_n(f+1)`.
The top-side argument is identical: reverse row height, and the source labels
again cycle with period `n`. No separate scramble is chosen for that side.

## Consequence for the scheduler's small ranks

Let `J=86000000` and `delta=128/4095<1/2`. Suppose

```
(f+1)*(f+2)/2 > J.
```

For every `j<=min(J,delta*f*n)`, the cyclic construction captures all marked
keys into the correct fringe:

- If `n>=f+1`, the triangular mass bound exceeds `J`.
- If `n<f+1`, then
  `M_n(f+1) > n*f/2 > delta*f*n`, exceeding the supported input mass.

The first integer `f` meeting the displayed triangular condition is `13114`:
`13115*13116/2=86008170>86000000`, whereas
`13114*13115/2=85995055`. Actual scheduler geometry imposes additional lattice
conditions; this scalar threshold is not a template construction.

Both candidate fringe sizes `131040` and `262080` clear this obstruction by a
large margin. Unlike the earlier probabilistic proposal, this argument needs
neither a relative intermediate error nor rank rounding. It covers only the
small-rank interval, not the required relative fringe guarantee for `j>J`.

## Bulk compatibility remains open

This cyclic scramble is not shown to satisfy the universal first-round bulk
theorem. It is unsafe to combine its deterministic fringe witness with an
unrelated bulk scramble witness.

There is a limited deterministic bulk estimate. For input column heights
`z_c`, a fixed destination receives either `floor(z_c/n)` or `ceil(z_c/n)`
marks from source `c`. Consequently each destination height differs from
the mean `sum(z_c)/n` by at most `n`. At exact mean `i`,

```
(1/n)*sum_c |s_c-i| <= n.
```

This is useful only when `n` is small relative to the desired first-round
allowance `e*m`. The global scheduler permits arbitrarily large `n`, so it
does not provide the uniform bulk premise used in the two-round Bernstein
argument. Also the cyclic family lacks independent row permutations, so the
existing probabilistic argument cannot be imported for it unchanged.

Appending an unrelated scramble before this capture step destroys the sorted
input promise unless another full column sort is charged. Appending arbitrary
row scrambles after lossless capture preserves the small-rank property, but
does not establish the missing bulk estimate on their input height profiles.

## Next meaningful target

Find a common scramble family with both:

1. a prefix/suffix source-occurrence bound strong enough to force
   `j>M_n(f+1)` (or another bound exceeding the supported small-rank mass)
   whenever a destination accumulates `f+1` marks; and
2. sufficiently strong universal bulk mixing for all scheduler column counts
   `n`, followed by the two-round bulk argument with an explicit repair reserve.

A successful family must also address large-rank fringe error and physical
depth. The deterministic construction shows that lossless small-rank capture
itself is feasible at these fringe sizes; it does not yet show compatibility
with the entire separator contract. The repair budget remains 193/107 layers,
and no fitting bulk repair is constructed here.
