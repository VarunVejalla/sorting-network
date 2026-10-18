"""Compare a fixed 17-layer matching order with graph matching capacity.

Requires NumPy and SciPy. Each sample has exactly one quarter of positions
marked high and one quarter marked hole, independently selected on the two
sides. The graph is the union of random perfect matchings. This is only a
diagnostic for that graph family and the iid two-row repair model.
"""

from __future__ import annotations

import argparse

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching


def run(wires: int, depth: int, samples: int, seed: int) -> None:
    if wires % 4:
        raise ValueError("--wires must be divisible by 4")
    rng = np.random.default_rng(seed)
    schedule = [rng.permutation(wires) for _ in range(depth)]

    # Sparse union graph. Repeated edges across layers are retained only once
    # for the graph-capacity computation; they remain repeated in the schedule.
    rows = np.tile(np.arange(wires), depth)
    cols = np.concatenate(schedule)
    graph = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)),
                       shape=(wires, wires))
    graph.data[:] = 1
    graph.eliminate_zeros()

    density = wires // 4
    greedy_residuals = []
    maximum_residuals = []
    isolated_highs = []
    for _ in range(samples):
        high = np.zeros(wires, dtype=bool)
        hole = np.zeros(wires, dtype=bool)
        high[rng.choice(wires, density, replace=False)] = True
        hole[rng.choice(wires, density, replace=False)] = True

        h = high.copy()
        l = hole.copy()
        for permutation in schedule:
            paired = h & l[permutation]
            h &= ~l[permutation]
            l[permutation] &= ~paired
        greedy_residuals.append(int(h.sum()))

        high_ids = np.flatnonzero(high)
        hole_ids = np.flatnonzero(hole)
        induced = graph[high_ids][:, hole_ids]
        matching = maximum_bipartite_matching(induced, perm_type="row")
        maximum_residuals.append(int(len(high_ids) - np.count_nonzero(matching >= 0)))

        neighbor_holes = np.asarray(graph @ hole.astype(np.int8)).reshape(-1)
        isolated_highs.append(int(np.count_nonzero(high & (neighbor_holes == 0))))

    norm = float(wires)
    print(f"wires={wires}, layers={depth}, samples={samples}, seed={seed}")
    print(f"mean isolated highs: {np.mean(isolated_highs):.3f} wires "
          f"({np.mean(isolated_highs)/norm:.6f} per position)")
    print(f"mean fixed-order residual highs: {np.mean(greedy_residuals):.3f} wires "
          f"({np.mean(greedy_residuals)/norm:.6f} per position)")
    print(f"mean maximum-matching residual highs: {np.mean(maximum_residuals):.3f} wires "
          f"({np.mean(maximum_residuals)/norm:.6f} per position)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, default=4096)
    parser.add_argument("--depth", type=int, default=17)
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20261011)
    args = parser.parse_args()
    run(args.wires, args.depth, args.samples, args.seed)


if __name__ == "__main__":
    main()
