# Designed round-1 scrambles: kill test for the light-tail lever (UB-09 follow-on 3)

Date: 2026-11-07. Claim level: **hand** (lower bound below) and **attack simulation**
(exact runs). No new sorting bound; the best proved coefficient is still 789.75.

## Verdict

The route is dead. No round-1 scramble design can make the tail lighter than about 0.16/W at
the nodes that set the stage depth. That is the same 1/W law as random scrambles, within a few
per cent. `STAGE-SCREEN.md` needed a tail about 1000× lighter. A design helps only when the
number of rows exceeds the number of columns (m > n). That holds only at small nodes; the top
nodes, which bind, have n ≫ m (`../../backlog/ruled-out.md`).

With the lever in `STAGE-SCREEN.md` gone, every stage built from column sorts and row
scrambles stays at or above about 333 (attack level, R2c). So sub-300 is out of reach in the
current binary Chvátal architecture at model level.

## Lower bound that holds for every design (hand)

Setting (as in `d2_bulk_attack.py`):
- The m × n matrix has column-sorted 0-1 input heights h.
- The scramble s1[r, u] gives the middle column that receives cell (r, u); each row is a
  permutation.
- Tail(W) = Σ_c (mid_c − mean − W)₊ / (mn).

Suppose each input column sends its m cells to distinct middle columns. That is possible only
when n ≥ m.

1. **Attack.** Pick any target set S with k = pn columns. Give each cell landing in S the price
   +1 and every other cell −p/(1−p). Each input column takes the height that maximises its walk
   of prices; call that maximum M_u. Since total_S − p·total equals (1−p)·walk for every
   column, summing gives exactly

   Σ_{c∈S}(mid_c − mean) = (1−p) Σ_u M_u.

2. **From excess to tail.** Every column satisfies (dev − W)₊ ≥ dev − W. Summing over S gives

   Tail(W) ≥ [(1−p) Σ_u M_u − W·pn] / (mn).

3. **Average over S.** Take S uniformly at random. Each column's membership sequence is then
   the first m entries of a random arrangement of k ones among n. Its law, and so E M_u, is the
   same for every design with distinct destinations.

So for every such design and every p, some S achieves Tail(W) ≥ [(1−p)·n·E M − W·pn]/(mn).
Optimising p, with E M ≈ √(2mp/π) for small p, gives about (1/2π)/W ≈ 0.16/W.

The distinct-destination assumption is the only gap. A design that repeats destinations within
a column when n ≥ m is not covered by this proof. Such a design confines a column's cells to
fewer middle columns, which works against mixing (see Limits).

## Attack measurements (`scripts/designed_scramble_screen.py`)

Each run is an exact run, so it is a lower bound for that scramble. The attack uses random
target sets and a design-aware set (the first pn destinations of column 0).

The designs:
- **random:** independent random row permutations.
- **affine:** a_r·u + b_r mod n, with n prime.
- **latin:** blocks of n rows, each a randomly isotoped cyclic Latin square, so every column
  visits every middle column once per block.
- **kronecker:** shifts u + ⌊n·frac(rφ)⌋, a low-discrepancy sequence.
- **cyclic:** u + r mod n.

Tail(W) at W = ½, 1, 2, 4 and 8 times √m:

| n, m | Row | ½√m | √m | 2√m | 4√m | 8√m |
|---|---|---:|---:|---:|---:|---:|
| 4099, 1024 (n > m) | certified tail_frac | 3.78e-2 | 3.00e-2 | 1.81e-2 | 7.25e-3 | 2.52e-3 |
| | hand bound (above) | 6.58e-3 | 3.92e-3 | 2.10e-3 | 1.10e-3 | 4.55e-4 |
| | random | 6.86e-3 | 4.24e-3 | 2.17e-3 | 1.07e-3 | 4.49e-4 |
| | affine | 6.78e-3 | 4.19e-3 | 2.14e-3 | 1.07e-3 | 4.54e-4 |
| | latin | 6.55e-3 | 3.93e-3 | 1.94e-3 | 9.77e-4 | 4.18e-4 |
| | kronecker | 1.40e-1 | 1.33e-1 | 1.19e-1 | 9.63e-2 | 5.87e-2 |
| | cyclic | 1.96e-1 | 1.90e-1 | 1.78e-1 | 1.55e-1 | 1.11e-1 |
| 8191, 2048 (n ≫ m) | hand bound | 4.53e-3 | 2.70e-3 | 1.50e-3 | 7.33e-4 | 3.23e-4 |
| | random | 4.79e-3 | 3.02e-3 | 1.55e-3 | 8.01e-4 | 3.51e-4 |
| | affine | 4.82e-3 | 3.04e-3 | 1.55e-3 | 7.96e-4 | 3.56e-4 |
| | latin | 4.51e-3 | 2.80e-3 | 1.40e-3 | 7.18e-4 | 3.23e-4 |
| | kronecker | 1.42e-1 | 1.37e-1 | 1.28e-1 | 1.10e-1 | 7.85e-2 |
| 1009, 8192 (m > n) | certified tail_frac | 1.34e-2 | 1.06e-2 | 6.40e-3 | 2.56e-3 | 8.92e-4 |
| | random | 2.48e-3 | 1.52e-3 | 7.96e-4 | 4.12e-4 | 1.97e-4 |
| | affine | 2.42e-3 | 1.51e-3 | 7.88e-4 | 4.24e-4 | 2.04e-4 |
| | latin | 6.74e-4 | 3.69e-4 | 2.00e-4 | 8.50e-5 | **0** |
| | kronecker | 1.42e-2 | 1.18e-2 | 7.89e-3 | 2.99e-3 | 6.0e-5 |
| | cyclic | 1.28e-2 | 1.03e-2 | 6.33e-3 | 1.23e-3 | **0** |

What the table shows:
- **n ≥ m.** The design-independent bound reproduces the attack on the random and Latin
  designs to within about 5%. So the random-target attack is the whole effect, and no unbiased
  design does better.
- **Structured designs.** Low-discrepancy shifts and cyclic designs are 30–300× worse. The
  adversary aligns input mass with the shift structure.
- **m > n.** Latin blocks cut the tail by 3–4× and then to zero beyond about n rows, because
  every column's walk resets after each block. Cyclic has the hard cutoff of Leighton's
  columnsort but is 5× worse below it. This gain exists only at small nodes.

## Limits

- **Height cap.** A height-capped round 1 isn't available: the input heights come from a full
  column sort and are arbitrary.
- **Confining columns.** Restricting each column to a group of g < m middle columns makes the
  group behave like the m > n case, but no mass moves between groups. The deviations from the
  global mean are then as large as the input imbalance. A second, cross-group round is again an
  n ≫ m round with the same 1/W tail. This argument is not simulated.
- **Attack depth.** One scramble per design, and the attack is not annealed. These are lower
  bounds; the n ≥ m conclusion rests on the hand bound, not on the attack.

Reproduce: `python scripts/designed_scramble_screen.py 4099 1024` (also `8191 2048` and
`1009 8192`), about 10 minutes each.
