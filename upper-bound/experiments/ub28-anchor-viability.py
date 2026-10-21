#!/usr/bin/env python3
"""Inspect exact support of the finite UB-28 terminal anchor.

For each requested output edge, reverse the exact width-4/2/1 suffix and the
actual randomized 150-round passes at widths 8 and 16. The max-plus table is
finite exactly on count profiles from which the specified edge inversion has
positive probability through that finite continuation. Its values are
floating log probabilities, but only finite-versus-minus-infinity status is
used here. This is a finite-width diagnostic, not the all-scale phase proof.
"""

import argparse
import importlib.util
from pathlib import Path
import time

import numpy as np


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "ub28_local_edge_maxpath", HERE / "ub28-local-edge-maxpath.py"
)
maxpath = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(maxpath)


def inspect(n: int, edge: int, rounds: int, cutoff_width: int) -> None:
    start = time.perf_counter()
    support, table, blocks = maxpath.edge_state_at_width(
        n, edge, rounds, cutoff_width
    )
    viable = int(np.isfinite(table).sum())
    total = table.size
    print(
        f"edge={edge} support={support} blocks={blocks} "
        f"viable={viable}/{total} "
        f"fraction={viable / total:.9g} "
        f"elapsed={time.perf_counter() - start:.2f}s",
        flush=True,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=256)
    parser.add_argument("--rounds", type=int, default=150)
    parser.add_argument("--cutoff-width", type=int, default=16)
    parser.add_argument(
        "--edges",
        default="0,1,2,6,14,30,62,126,254",
        help="comma-separated output edge indices",
    )
    args = parser.parse_args()
    if args.n < 32 or args.n & (args.n - 1):
        raise ValueError("n must be a power of two at least 32")
    edges = [int(value) for value in args.edges.split(",") if value]
    if any(edge < 0 or edge >= args.n - 1 for edge in edges):
        raise ValueError("each edge must lie in [0,n-2]")
    for edge in edges:
        inspect(args.n, edge, args.rounds, args.cutoff_width)


if __name__ == "__main__":
    main()
