# Sorting Network Project — Source List
**Date:** 2026-09-04

These are the main references used in the conversation.

## 1. V. Chvátal — *Lecture Notes on the New AKS Sorting Network*
Primary source for:
- explicit \(1830\) binary-comparator upper constant;
- separator framework;
- Properties B and F;
- \(M\)-sorter coefficient \(48\);
- optimized \(24+16\sqrt2\);
- framework barrier \(12+8\sqrt2\approx23.3137\);
- report of Komlós's private \(<10\) \(M\)-sorter claim and \(\sim60\)–\(100\) binary claim.

URL:
https://users.encs.concordia.ca/~chvatal/aks.pdf

Rutgers metadata:
https://scholarship.libraries.rutgers.edu/esploro/outputs/technicalDocumentation/Lecture-Notes-on-the-New-AKS/991031550235304646

## 2. M. Ajtai, J. Komlós, E. Szemerédi — *An O(n log n) Sorting Network*
Primary source for:
- original AKS Zig/Zag/cherry architecture;
- multiscale register bookkeeping;
- wrongness concept;
- informal statement that three partitions per time cycle (Zig–Zag–Zig) suffice.

ResearchGate PDF used in the conversation:
https://www.researchgate.net/profile/Janos-Komlos/publication/221590321_An_On_log_n_Sorting_Network/links/5ebcfeff458515626ca8032f/An-On-log-n-Sorting-Network.pdf

## 3. M. Ajtai, J. Komlós, E. Szemerédi — *Halvers and Expanders*
FOCS 1992.
Primary source for:
- depth-2 large-sorter halvers;
- error scale \(O(\sqrt{\log k/k})\);
- direct multiway partitioning idea;
- clue toward unpublished `k-sorting` work.

DOI / IEEE:
https://doi.org/10.1109/SFCS.1992.267782
https://ieeexplore.ieee.org/document/267782

ResearchGate PDF used in the conversation:
https://www.researchgate.net/profile/Janos-Komlos/publication/3513473_Halvers_and_expanders_switching/links/5ebcfc52299bf1c09abbdb79/Halvers-and-expanders-switching.pdf

## 4. Seiferas — *Sorting Networks of Logarithmic Depth, Further Simplified*
Used for:
- historical discussion of AKS simplifications;
- discussion of Komlós's unpublished/private constants;
- stranger/error recurrences and benchmark-distribution bookkeeping.

University of Rochester copy encountered:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=3258&itemId=2353

## 5. Kahale et al. — lower bound around 3.27
Used for the best known asymptotic lower constant on sorting-network depth.

NYU-hosted PDF encountered:
https://research.engineering.nyu.edu/~suel/papers/size.pdf

## 6. 2024 paper — Dobrokhotova-Maikova, Kozachinskiy, Podolskii
Used only as a modern comparison for staggered/overlapping block decompositions; it does **not** by itself give the desired \(O(\log n)\) fixed-arity depth constant.

LIPIcs PDF:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol317-approx-random2024/LIPIcs.APPROX-RANDOM.2024.50/LIPIcs.APPROX-RANDOM.2024.50.pdf

---

## Source-status caution

The candidate \(24+o(1)\) theorem in the handoff is **not a published theorem located in these sources**. It is a new candidate construction developed in the conversation by combining:
- AKS Zig/Zag multiscale architecture,
- Chvátal-style register/fringe analysis,
- depth-2 large-sorter multiway partitioning,
- a new safe/rogue + nested-fringe invariant.

The fresh conversation should treat it as a proof project requiring a full global audit before claiming a new result.
