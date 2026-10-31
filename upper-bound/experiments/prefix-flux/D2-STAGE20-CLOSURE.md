# Stage 20 reserve-invariant closure

Focused Lean source checks pass for the Stage-20 frontier and all actual input
contracts at levels 8, 6, 4, 2, and 0. `D2Stage20PreservesInv.lean` composes
them into the Run-20-to-Run-21 reserve-invariant transition for every depth
`d >= 16`.

The bottom gate reuses the Stage-19 level-seven regular-child bound and the
native level-nine tail. Moving upward, the Stage-19 quotas at levels 7, 5,
and 3 give 15-fold endpoint floors for Stage-20 levels 6, 4, and 2. The
level-two startup at `d = 16` is top-descending with an exact-zero root; at
larger depths level two is middle. Stage 20's root is inactive at depth 16;
otherwise it is top-descending and keeps the zero root preserved from Stage
18 through Stage 19.

This closes one more finite scheduled transition only. It does not supply an
arbitrary-stage induction/provider, prove physical rank/port realization,
establish terminal exact sorting, or complete the logarithmic-depth accounting.
The unconditional claim `limsup D(n)/log2(n) <= 300` remains unproved.
