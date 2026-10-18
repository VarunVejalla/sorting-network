# Test: can the 2024 s-sorted invariant replace exact column sorting?

Reviewed 2026-10-10 against the current `upper-bound/best` two-round separator.
This is a proof-interface audit, not a new construction or a formalized theorem.

## Result

The paper's invariant does not plug into the current separator as a drop-in
replacement for exact column sorting. It remains a useful design idea for a
new separator, but the present bulk and fringe guarantees are much sharper
than the generic error control supplied by s-sortedness.

The current proof first converts thresholded Boolean inputs to
`MonotoneColumnSums`. The bulk probability/counting arguments quantify over
those exact monotone columns; the bridge uses the fact that the first
`columnSortNetwork` output is column-monotone. The physical network then
performs exact column sorts between row scrambles. This is a structural input
to the existing proof, not merely an implementation detail.

## Quantitative perturbation screen

For a Boolean column that is s-sorted in the paper's sense, replacing it by
the monotone column with the same number of ones changes at most s entries:
outside its one uncertain interval, the column already agrees with that
canonical version. Thus an m-by-n matrix is within Hamming distance at most
n*s of an exactly monotone-column matrix.

Comparator networks are nonexpansive in Hamming distance on Boolean inputs:
each comparator maps a pair to its sorted pair, and cannot increase the
number of differing bits between two paired inputs. Hence this comparison
can contribute as much as n*s changed output cells. The ordinary-node bulk
budget is `EB = a/(2*59,000,000) = mn/118,000,000`. Absorbing the generic
perturbation into that budget would require

    s <= m / 118,000,000,

before reserving any of the budget for the existing proof's own errors. The
paper's merge lemma gives `s' <= p*s + 2*n*p/t`; its recursive construction
gives uncertainty on the order of `n log_t(n)/t`. Those are useful relative
error bounds for its own recursion, but the current separator needs an
extraordinarily small error fraction at each ordinary node. The paper does
not establish this scale for a compatible column operation.

The fringe condition is a harder obstruction. The current node requires,
for every `1 <= j <= Jmax`, fewer than `j/86,000,000` extreme keys outside
the fringe. Since this is below one for all supported j, the integer number
of misses must be exactly zero throughout that range. A generic Hamming
perturbation bound—even one far smaller than the bulk allowance—cannot certify
this exact rare-rank behavior. The paper's s-sorted invariant controls one
interval's width, not the location of each of the top/bottom rare keys in the
separator's required fringe.

## What remains promising

The 2024 construction is still relevant to a fundamentally redesigned local
separator: its localized uncertainty interval is a richer state than a single
bulk error rate, and the paper explicitly composes such states using
multi-input sorting gates (Lemma 18) and recursive k-sorting (Lemma 19). To
reuse that idea here, a new proof would need to propagate both (i) bulk
misplacement at the paper's tiny scale and (ii) exact or suitably relative
extreme-rank placement through each stage. The current interface supplies
neither from s-sortedness alone.

The next useful experiment is therefore not replacing `columnSortNetwork`
inside `physicalPack2Net`. It is to formulate a localized-uncertainty node
contract that directly implies the scheduler's `bHigh/bLow/fHigh/fLow`
obligations, then see whether a finite multiway construction can meet it.

## Sources and status

- Published source: Dobrokhotova-Maikova, Kozachinskiy, Podolskii, “Towards
  Simpler Sorting Networks and Monotone Circuits for Majority,” APPROX/RANDOM
  2024, Definition 16 and Lemmas 18–19:
  [paper PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol317-approx-random2024/LIPIcs.APPROX-RANDOM.2024.50/LIPIcs.APPROX-RANDOM.2024.50.pdf).
- Current proof sources: `SortedColumnDecode.lean`, `Bulk2Bridge.lean`,
  `PhysicalPack2.lean`, `NodeSpec.lean`, `KernelSetup.lean`, and
  `Theorem51Core.lean` in `upper-bound/best/AKS/Chvatal`.
- The Hamming perturbation estimate and compatibility assessment above are
  deductions from these definitions, not statements proved in Lean.
