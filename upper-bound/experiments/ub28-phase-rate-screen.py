#!/usr/bin/env python3
"""Coarse rate screen over support and exact-tail phases for UB-28.

This is a diagnostic only: it samples one edge per exact support phase and
uses the feasible grid count lattice, so rates above ln(2) are not upper
bounds on the full trajectory maximum. Representatives combine the support
closure phase with the exact terminal-window signature. This remains a
diagnostic, not a coverage proof or a certified Bellman bound.
"""

import argparse
import importlib.util
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


phase = load("ub28_phase_closure", "ub28-phase-closure.py")
terminal = load("ub28_terminal_window", "ub28-terminal-window-language.py")
rate = load("ub28_rate_grid", "ub28-rate-grid.py")


def phase_representatives():
    width4_blocks = 64  # The exact finite anchor has 256 wires.
    output = terminal.output_supports(width4_blocks)
    blocks = width4_blocks // 2
    representatives = {}
    for edge in range(4 * width4_blocks - 1):
        support = {index // 2 for index in output[edge] | output[edge + 1]}
        first, last = min(support), max(support)
        for offset in (1, 0):
            first, last = phase.close_interval(first, last, blocks, offset)
        key = phase.phase_from_interval(first, last - first + 1, blocks)
        # Support closure controls the earlier scale transitions. The exact
        # terminal forbidden-window table has its own periodic edge language;
        # retain both keys so a support representative cannot silently stand
        # in for a different terminal event.
        terminal_key = terminal.signature(edge, output[edge] | output[edge + 1])
        representatives.setdefault((key, terminal_key), edge)
    return representatives


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log-n", type=int, default=12)
    parser.add_argument("--grid", type=int, default=4)
    parser.add_argument("--high", type=int, default=280)
    parser.add_argument("--low", type=int, default=20)
    parser.add_argument("--native-dll",
                        help="optional compiled ub28-maxplus-kernel shared library")
    parser.add_argument("--limit", type=int, default=0,
                        help="run only the first N representative phases (0 means all)")
    parser.add_argument("--edge", type=int,
                        help="run only the representative for this exact anchor edge")
    parser.add_argument("--list-only", action="store_true",
                        help="print support-phase representatives and exit")
    parser.add_argument("--placements", nargs="+", choices=("left", "center", "right"),
                        default=("left", "center", "right"))
    args = parser.parse_args()
    if args.native_dll:
        rate.enable_native_kernel(args.native_dll)

    reps = phase_representatives()
    items = sorted(reps.items(), key=lambda item: item[1])
    if args.list_only:
        for key, edge in items:
            print(f"edge={edge} support_phase={key[0]} terminal_phase={key[1]}")
        return
    if args.edge is not None:
        items = [item for item in items if item[1] == args.edge]
        if not items:
            parser.error(f"edge {args.edge} is not a composite phase representative")
    if args.limit:
        items = items[:args.limit]
    print(f"composite_phases={len(reps)} running={len(items)}", flush=True)
    results = []
    for key, edge in items:
        for placement in args.placements:
            value = rate.asymptotic_rate(
                args.log_n, 70, args.grid, edge,
                top_alternating=True, top_high=args.high, top_low=args.low,
                placement=placement, exact_anchor=True,
            )
            results.append((value, edge, placement, key))
            print(f"edge={edge:3d} placement={placement:6s} rate={value:.12g}",
                  flush=True)
    worst = min(results)
    print(f"min_sampled_rate={worst[0]:.12g} ln2={math.log(2):.12g} "
          f"edge={worst[1]} placement={worst[2]}")


if __name__ == "__main__":
    main()
