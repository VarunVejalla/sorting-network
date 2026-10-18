# A threshold-count contract for a shallow final repair

Research note, 2026-10-10. The deductions below are unaudited mathematics,
not Lean theorems. No sorting bound is improved. The source contracts used are
`NodeSpec`, `MatrixBridge`, `SortedColumnDecode`, and `PackSpec` in
`upper-bound/best/AKS/Chvatal`.

## Exact comparison with a full column sort

Fix an `m × n` node and the Boolean state `u` immediately before the final
column operation. For a bottom-region height `i`, write

```
Q_R(u,i) = number of true cells in rows r < m-i after repair R,
Q_*(u,i) = sum over columns c of (s_c-i)_+,
```

where `s_c` is the number of true cells of `u` in column `c`. By
`matrixOnesCountInRegion_colSort_eq_sum_columnSub`, `Q_*` is exactly the count
after a full column sort. Thus a convenient harmful defect is

```
D_R(u,i) = max(0, Q_R(u,i)-Q_*(u,i)).
```

The downstream comparison is the one-sided inequality
`Q_R(u,i) <= Q_*(u,i)+d`. If `R` is column-local, it preserves every `s_c`, and
`Q_*` is the minimum possible number of true cells above the cut: the bottom
`i` cells of a column accommodate at most `i` of its `s_c` true cells. Hence
`Q_R >= Q_*`, the raw defect is nonnegative, and `D_R=Q_R-Q_*`. For an
arbitrary repair with cross-column comparators, `Q_R` can instead be smaller
than this particular full-sort baseline. Absolute error and column
monotonicity are stronger than the scheduler's count interface requires.
Merely preserving column counts is insufficient: without sorting, those same
counts can place additional true cells above the cut.

The low-key orientation is a separate instance. Directly marking the smallest
keys as `true` is antitone in the key and therefore does not commute with
ascending compare-exchange through the monotone-threshold lemma used by
`PackSpec`. One may instead mark the complement (the nonsmall keys) and count
zeros in the bottom region, or prove an explicit transformation combining key
order reversal, Boolean complement, and row reflection and then apply the
high-side statement. This symmetry must be proved for the proposed physical
repair; it cannot be inferred for an arbitrary network.

## The cuts and ranks actually consumed

For node geometry `m = 2f+64b`, `a=mn`, `up=2fn`, and `down=bn`, every bulk
boundary in `NodeSpec` has

```
p_k = (f+k b)n,       i_k = f+k b,       k=0,...,64.
```

The high-side threshold selects the largest `p_k=i_k n` keys and is read above
the bottom `i_k` rows. Therefore the complete bulk repair obligation is the 65
simultaneous inequalities

```
Q_R(u(x,p_k),i_k) <= Q_*(u(x,p_k),i_k) + d_B(x,k)
```

for every permutation input `x`, in both orientations. Here `u(x,t)` is the
pre-repair Boolean state obtained by thresholding at rank `t`; comparator
execution commutes with this monotone thresholding.

The fringe uses one spatial cut, `i=f`, but every rank

```
1 <= j <= Jmax = specJmax(up).
```

Its complete obligation is

```
Q_R(u(x,j),f) <= Q_*(u(x,j),f) + d_F(x,j)
```

for every permutation `x`, every supported `j`, and both orientations. A
contract only at the 65 bulk thresholds does not imply this all-rank fringe
contract.

These are the `all65bulk` cuts and `allfringe` ranks in semantic form. They are
sufficient for the current `PackSpec` bridge because every bulk cut is row
aligned. They make no claim about arbitrary cuts inside a row.

## Exact integer slack

Let `E_B` denote the real `NodeSpec.bHigh` allowance (`specEB` in the scheduler)
and let `e = epsF`. Since all threshold counts are natural numbers, the exact
available repair budgets for a fixed input are

```
S_B(x,k) = floor(E_B) - Q_*(u(x,p_k),i_k),
S_F(x,j) = ceil(e j) - 1 - Q_*(u(x,j),f).
```

Treat these as integer-valued expressions, so a negative value records that
the full-sort baseline itself misses the target. Provided `S_B >= 0` and
`S_F >= 0`, respectively, the repaired output satisfies the required contract
precisely when

```
D_R(u(x,p_k),i_k) <= S_B(x,k),
D_R(u(x,j),f)     <= S_F(x,j).
```

Without that premise the equivalence fails for a repair with cross-column
movement: such a repair can outperform the chosen full-sort baseline and meet
the target even though `D_R <= S` is false. For a column-local repair this case
cannot rescue the target because `Q_R >= Q_*`.

The second formula is where strictness matters: for an integer `q`,
`q < e j` is equivalent to `q <= ceil(e j)-1`, including when `e j` is an
integer. Replacing the ceiling by a floor is wrong at integral endpoints. For
bulk, whose target is non-strict, `q <= E_B` is equivalent to
`q <= floor(E_B)`.

The present upstream results state `Q_* < E_B` for bulk and `Q_* < e j` for
fringe. From strict bulk alone the uniformly guaranteed integer slack is only
one when `E_B` is an integer and zero when it is not. From strict fringe alone
the guaranteed slack is zero. In particular, with `e=1/86000000`, every
`j <= 86000000` has fringe budget zero and the repair must introduce no escape
at all. A positive repair allowance therefore requires the probability or
counting proof to establish a correspondingly stronger bound, not merely the
current strict inequality.

## A sufficient slack interface

A usable theorem can expose nonnegative integer budgets `rhoB` and `rhoF` and
prove, for one fixed repair network `R`, all of the following simultaneously:

```
full-sort bulk count + rhoB(x,k) <= floor(E_B),
repair bulk defect             <= rhoB(x,k),

full-sort fringe count + rhoF(x,j) <= ceil(e j)-1,
repair fringe defect               <= rhoF(x,j),
```

for every input, all 65 bulk indices, all supported fringe ranks, and both
orientations. The budgets may depend on the input and index; the network may
not. A coarser uniform version with constants `rhoB0,rhoF0` is sufficient if
the first pair of inequalities is proved with those uniform margins. For the
small-rank fringe range the only possible uniform choice is `rhoF0=0`.

This sufficient interface isolates the two proof tasks cleanly: the two-round mixing
argument supplies full-sort counts with explicit integer reserve, while the
physical shallow repair consumes no more than that reserve. A more general
cross-column proof may establish `Q_R` against the target directly and need
not pass through the full-sort baseline.

## Quantifier traps

The same physical comparator network, including the same scramble and repair
witnesses, must satisfy every item above. Separate existence statements for
each cutoff, rank, orientation, or input cannot be combined into `NodeSpec`.
Likewise, a probabilistic argument may union-bound over a finite family of
input classes only after proving that those classes cover every pre-repair
threshold state generated by every permutation input. The bulk exact-mass
classes (`p_k=i_k n`) and fringe exact-rank classes (`j`) are different
families; proving a witness for one family does not cover the other.

There is a second input-class trap. The repair theorem need not quantify over
all Boolean matrices. Its reachable class may legitimately depend on the
chosen scrambles: the intended order is

```
exists sigma1, sigma2, R, for every permutation x and every required threshold,
  the resulting state lies in Reach(sigma1,sigma2) and satisfies the bound.
```

What is invalid is selecting a separate witness for each input or defining a
post hoc class that omits an adversarial state actually reachable under the
fixed witnesses. The class theorem must uniformly cover all states generated
by every input and required threshold once `sigma1`, `sigma2`, and `R` are
fixed.

Finally, the semantic count theorem must be connected to the physical network
with its cumulative row relabeling, as `PhysicalPack` and `PackSpec` do for the
full sorter. A semantic repair bound alone does not establish the positional
counts in `NodeSpec`.

## Decision criterion

A proposed shallow repair is compatible with the present scheduler exactly
when it comes with the simultaneous high/low `all65bulk` and `allfringe`
one-sided defect bounds above, an upstream proof of enough integer slack, and a
physical implementation within the stage budget. Without explicit slack, the
current contracts permit no fringe defect and generally no bulk defect.
