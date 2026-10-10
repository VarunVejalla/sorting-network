# References and Links

## Core repository

- `girving/aks`:
  https://github.com/girving/aks

Current public README (checked 2026-09-27) describes:
- Lean formalization of Seiferas's simplified AKS proof;
- top-level depth constant \(141\cdot10^{62}\);
- MGG expander → squaring → halver → separator → bag-tree path;
- Paterson as an explicit future improvement direction.

## Core papers

### 1. Ajtai, Komlós, Szemerédi — *An O(n log n) Sorting Network*

Original AKS construction.

Repository reference / ACM DL is linked from the `girving/aks` README.

Previously used copy:
https://www.researchgate.net/profile/Janos-Komlos/publication/221590321_An_On_log_n_Sorting_Network/links/5ebcfeff458515626ca8032f/An-On-log-n-Sorting-Network.pdf

### 2. Mike Paterson — *Improved Sorting Networks with O(log N) Depth*

Algorithmica 5 (1990), 75–92.

Open Warwick archive:
https://wrap.warwick.ac.uk/60785/

PDF:
https://wrap.warwick.ac.uk/id/eprint/60785/12/WRAP_cs-rr-89.pdf

This is the preferred near-term improvement source. The `girving/aks` README states that Paterson's construction achieves depth `< 6100 log n`.

### 3. V. Chvátal — *Lecture Notes on the New AKS Sorting Network*

Used for explicit constants, separator framework, Properties B/F, and the 1830 bound.

PDF:
https://users.encs.concordia.ca/~chvatal/aks.pdf

Rutgers metadata:
https://scholarship.libraries.rutgers.edu/esploro/outputs/technicalDocumentation/Lecture-Notes-on-the-New-AKS/991031550235304646

### 4. Joel Seiferas — *Sorting Networks of Logarithmic Depth, Further Simplified*

Main backbone of the current Lean repository's bag-tree correctness proof.

University of Rochester copy previously used:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=3258&itemId=2353

### 5. Ajtai, Komlós, Szemerédi — *Halvers and Expanders*

FOCS 1992.

DOI:
https://doi.org/10.1109/SFCS.1992.267782

IEEE:
https://ieeexplore.ieee.org/document/267782

Previously used copy:
https://www.researchgate.net/profile/Janos-Komlos/publication/3513473_Halvers_and_expanders_switching/links/5ebcfc52299bf1c09abbdb79/Halvers-and-expanders-switching.pdf

Role:
- depth-2 large-sorter halvers;
- error scaling;
- direct multiway partitioning inspiration.

## Repo-specific expander sources

### Margulis (1973)

*Explicit constructions of expanders.*

Used by the current repo as part of the MGG explicit expander.

### Gabber–Galil (1981)

*Explicit constructions of linear-sized superconcentrators.*

Combined with Margulis for the repo's explicit 8-regular expander.

These papers are important for the **current implementation**, but are not conceptually essential to our intended improved construction if Paterson or another better local primitive replaces the MGG route.

## Lower-bound / comparison references

The prior source list includes Kahale et al. for an asymptotic lower-bound constant around 3.27 and a 2024 paper by Dobrokhotova-Maikova, Kozachinskiy, Podolskii used only as a comparison for staggered block decompositions.

See:
`prior_handoffs/SORTING_NETWORK_SOURCES_2026-09-04.md`

## Bibliographic caution

The exact publication metadata for Paterson appears with minor page-number discrepancies across web indexes. The `girving/aks` repository cites:

> Algorithmica 5(1), 75–92 (1990)

Use the paper itself / DOI metadata when creating a formal bibliography.

## Do not overread reported constants

Numbers such as:

- 1830 (Chvátal),
- `<6100` (Paterson, as reported by the repo),
- much smaller Seiferas/Komlós historical claims,

come from different architectures and parameter conventions.

When formalizing, always derive the final constant from the exact theorem implemented in Lean rather than transplanting a headline number.
