#!/usr/bin/env python3
"""Heuristic area adversary for the targeted sparse-edge row repair.

The first rounds use fixed random row permutations. The final round uses its
random permutation on middle rows and a descending row sort plus fixed
rotation on the first/last edge_rows. This is a heuristic search, not a
universal certificate.
"""
import argparse
import random

from local_core_multiround_adversary import make_scrambles
from d2_sparse_row_spread_gate import packing_offsets

EDGE_ROWS = 40
ROW_STEP = 41


def stage(heights, permutations):
    out = [0] * len(heights)
    for source, height in enumerate(heights):
        for row in range(height):
            out[permutations[row][source]] += 1
    return out


def repaired_final(heights, middle_permutations, edge_rows, row_step, packing):
    rows, columns = len(middle_permutations), len(heights)
    out = [0] * columns
    offsets = packing_offsets(edge_rows) if packing else None
    for row in range(rows):
        if row < edge_rows:
            width = sum(height > row for height in heights)
            start = offsets[row] if packing else row_step * row % columns
            for offset in range(width):
                out[(start + offset) % columns] += 1
        elif row >= rows - edge_rows:
            if packing:
                bottom_row = rows - 1 - row
                start = offsets[bottom_row]
                for source, height in enumerate(heights):
                    if height > row:
                        out[(start + columns - 1 - source) % columns] += 1
            else:
                width = sum(height > row for height in heights)
                start = row_step * row % columns
                for offset in range(width):
                    out[(start + offset) % columns] += 1
        else:
            for source, height in enumerate(heights):
                if height > row:
                    out[middle_permutations[row][source]] += 1
    return out


def area(final, total, columns):
    q, r = divmod(total, columns)
    balanced = (columns - r) * q * q + r * (q + 1) ** 2
    return (sum(x * x for x in final) - balanced) // 2


def initial_state(heights, scrambles, edge_rows, row_step, packing):
    profiles = [heights.copy()]
    for permutations in scrambles[:-1]:
        profiles.append(stage(profiles[-1], permutations))
    final = repaired_final(profiles[-1], scrambles[-1], edge_rows, row_step,
                           packing)
    total = sum(heights)
    return profiles, final, total, area(final, total, len(heights))


def endpoint(source, direction, profiles, scrambles, edge_rows, row_step,
             packing):
    current = source
    for t in range(len(scrambles) - 1):
        height = profiles[t][current]
        row = height if direction > 0 else height - 1
        current = scrambles[t][row][current]
    height = profiles[-1][current]
    row = height if direction > 0 else height - 1
    if row < edge_rows:
        width = sum(x > row for x in profiles[-1])
        start = packing_offsets(edge_rows)[row] if packing else row_step * row % len(profiles[-1])
        dest = ((start + width) % len(profiles[-1]) if direction > 0 else
                (start + width - 1) % len(profiles[-1]))
    elif row >= len(scrambles[-1]) - edge_rows:
        width = sum(x > row for x in profiles[-1])
        if packing:
            bottom_row = len(scrambles[-1]) - 1 - row
            start = packing_offsets(edge_rows)[bottom_row]
            dest = ((start + len(profiles[-1]) - 1 - width) % len(profiles[-1])
                    if direction > 0 else
                    (start + len(profiles[-1]) - width) % len(profiles[-1]))
        else:
            start = row_step * row % len(profiles[-1])
            dest = ((start + width) % len(profiles[-1]) if direction > 0 else
                    (start + width - 1) % len(profiles[-1]))
    else:
        dest = scrambles[-1][row][current]
    return current, row, dest


def apply_change(source, direction, profiles, final, total, scrambles,
                 edge_rows, row_step, packing):
    current, row, dest = endpoint(source, direction, profiles, scrambles,
                                  edge_rows, row_step, packing)
    if direction > 0:
        delta = final[dest] - total // len(final)
    else:
        delta = (total + len(final) - 1) // len(final) - final[dest]

    profiles[0][source] += direction
    position = source
    for t in range(len(scrambles) - 1):
        old_height = profiles[t][position] - direction
        wire_row = old_height if direction > 0 else old_height - 1
        destination = scrambles[t][wire_row][position]
        profiles[t + 1][destination] += direction
        position = destination
    final[dest] += direction
    return total + direction, delta


def climb(start, scrambles, max_moves=100000, edge_rows=EDGE_ROWS,
          row_step=ROW_STEP, packing=False):
    profiles, final, total, value = initial_state(start, scrambles, edge_rows,
                                                   row_step, packing)
    moves = 0
    while moves < max_moves:
        best_delta, best_move = 0, None
        for source in range(len(start)):
            if profiles[0][source] < len(scrambles[0]):
                _, _, dest = endpoint(source, 1, profiles, scrambles,
                                      edge_rows, row_step, packing)
                delta = final[dest] - total // len(final)
                if delta > best_delta:
                    best_delta, best_move = delta, (source, 1)
            if profiles[0][source] > 0:
                _, _, dest = endpoint(source, -1, profiles, scrambles,
                                      edge_rows, row_step, packing)
                delta = (total + len(final) - 1) // len(final) - final[dest]
                if delta > best_delta:
                    best_delta, best_move = delta, (source, -1)
        if best_move is None:
            break
        source, direction = best_move
        total, delta = apply_change(source, direction, profiles, final,
                                    total, scrambles, edge_rows, row_step,
                                    packing)
        value += delta
        moves += 1
        if moves % 1000 == 0:
            full_profiles, full_final, full_total, full_value = initial_state(
                profiles[0], scrambles, edge_rows, row_step, packing)
            assert full_profiles == profiles
            assert full_final == final
            assert full_total == total and full_value == value
    full_profiles, full_final, full_total, full_value = initial_state(
        profiles[0], scrambles, edge_rows, row_step, packing)
    assert full_profiles == profiles
    assert full_final == final, ([(i, a, b) for i, (a, b) in
                                  enumerate(zip(full_final, final)) if a != b],
                                 profiles[-1], total)
    assert full_total == total and full_value == value
    return {"area": value, "fraction": value / (len(final) * len(scrambles[0])),
            "mass": total, "moves": moves, "input_heights": profiles[0],
            "output_heights": final}


def run(rows=4096, columns=64, seed=0, restarts=8, max_moves=100000,
        rounds=3, edge_rows=EDGE_ROWS, row_step=ROW_STEP, verbose=False,
        show_profile=False, packing=False):
    scrambles = make_scrambles(rows, columns, seed, rounds)
    rng = random.Random(seed + 20261025)
    results = []
    for restart in range(restarts):
        if restart == 0:
            start = [rows // 2] * columns
        else:
            start = [rng.randrange(rows + 1) for _ in range(columns)]
        result = climb(start, scrambles, max_moves, edge_rows, row_step,
                       packing)
        results.append(result)
        if verbose:
            print({"restart": restart, "area": result["area"],
                   "fraction": result["fraction"], "mass": result["mass"],
                   "moves": result["moves"]}, flush=True)
    best = max(results, key=lambda x: x["area"])
    summary = {"best_area": best["area"],
               "best_fraction": best["fraction"], "rounds": rounds,
               "edge_rows": edge_rows, "row_step": row_step,
               "packing": packing,
               "best_mass": best["mass"], "moves": best["moves"],
               "starts": restarts, "seed": seed}
    if show_profile:
        summary["input_heights"] = best["input_heights"]
        summary["output_heights"] = best["output_heights"]
    print(summary, flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int, default=4096)
    parser.add_argument("--columns", type=int, default=64)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--restarts", type=int, default=8)
    parser.add_argument("--max-moves", type=int, default=100000)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--edge-rows", type=int, default=EDGE_ROWS)
    parser.add_argument("--row-step", type=int, default=ROW_STEP)
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--show-profile", action="store_true")
    parser.add_argument("--packing", action="store_true",
                        help="use packed top prefixes and reflected bottom suffixes")
    args = parser.parse_args()
    run(args.rows, args.columns, args.seed, args.restarts, args.max_moves,
        args.rounds, args.edge_rows, args.row_step, args.verbose,
        args.show_profile, args.packing)
