#!/usr/bin/env python3
"""Coordinate-ascent adversary for a fixed two-scramble local core.

The input is represented by column heights after the mandatory first sort.
Each trial keeps both row scrambles fixed while optimizing the final
full-row-defect area. This searches for counterexamples to a small aggregate
budget; failure to find one is not an all-profile proof.
"""
import argparse
import math
import random


def make_inverse_scrambles(rows, columns, seed):
    rng = random.Random(seed)
    out = []
    for _ in range(2):
        scramble = []
        for _row in range(rows):
            perm = rng.sample(range(columns), columns)  # destination -> source
            inverse = [0] * columns
            for destination, source in enumerate(perm):
                inverse[source] = destination
            scramble.append(inverse)  # source -> destination
        out.append(scramble)
    return out


def evaluate(heights, scrambles):
    rows, columns = len(scrambles[0]), len(heights)
    first = [0] * columns
    for source, height in enumerate(heights):
        for row in range(height):
            first[scrambles[0][row][source]] += 1
    final = [0] * columns
    for source, height in enumerate(first):
        for row in range(height):
            final[scrambles[1][row][source]] += 1
    total = sum(heights)
    quotient, remainder = divmod(total, columns)
    balanced_square_sum = ((columns - remainder) * quotient**2
                           + remainder * (quotient + 1)**2)
    area = (sum(value * value for value in final) - balanced_square_sum) // 2
    return first, final, total, area


def change_height(heights, first, final, total, area, source, direction,
                 scrambles):
    columns = len(heights)
    if direction > 0:
        row = heights[source]
        col1 = scrambles[0][row][source]
        col2 = scrambles[1][first[col1]][col1]
        delta = final[col2] - total // columns
        first[col1] += 1
        final[col2] += 1
        total += 1
    else:
        row = heights[source] - 1
        col1 = scrambles[0][row][source]
        col2 = scrambles[1][first[col1] - 1][col1]
        delta = (total + columns - 1) // columns - final[col2]
        first[col1] -= 1
        final[col2] -= 1
        total -= 1
    heights[source] += direction
    return total, area + delta


def climb(heights, scrambles, verify_updates=False):
    rows, columns = len(scrambles[0]), len(heights)
    first, final, total, area = evaluate(heights, scrambles)
    moves = 0
    while True:
        best_delta, best_move = 0, None
        for source in range(columns):
            if heights[source] < rows:
                row = heights[source]
                col1 = scrambles[0][row][source]
                col2 = scrambles[1][first[col1]][col1]
                delta = final[col2] - total // columns
                if delta > best_delta:
                    best_delta, best_move = delta, (source, 1, col1, col2)
            if heights[source] > 0:
                row = heights[source] - 1
                col1 = scrambles[0][row][source]
                col2 = scrambles[1][first[col1] - 1][col1]
                delta = (total + columns - 1) // columns - final[col2]
                if delta > best_delta:
                    best_delta, best_move = delta, (source, -1, col1, col2)
        if best_move is None:
            break
        source, direction, _, _ = best_move
        old_area = area
        total, area = change_height(
            heights, first, final, total, area, source, direction, scrambles
        )
        assert area == old_area + best_delta
        moves += 1
        if verify_updates:
            assert evaluate(heights, scrambles) == (first, final, total, area)
    assert evaluate(heights, scrambles) == (first, final, total, area)
    return area, heights, total, moves


def anneal(heights, scrambles, seed, steps, verify_updates=False):
    rows, columns = len(scrambles[0]), len(heights)
    rng = random.Random(seed)
    first, final, total, area = evaluate(heights, scrambles)
    best = (area, heights.copy(), total)
    start_temp = max(1.0, rows / 2)
    for step in range(steps):
        source = rng.randrange(columns)
        target = rng.randrange(rows + 1)
        if target == heights[source]:
            continue
        old_height = heights[source]
        old_first, old_final = first.copy(), final.copy()
        old_total, old_area = total, area
        direction = 1 if target > old_height else -1
        while heights[source] != target:
            total, area = change_height(
                heights, first, final, total, area, source, direction,
                scrambles,
            )
        if verify_updates:
            assert evaluate(heights, scrambles) == (first, final, total, area)
        if area > best[0]:
            best = (area, heights.copy(), total)
        temperature = start_temp * (0.01 ** (step / max(1, steps)))
        if area < old_area and rng.random() >= math.exp(
                (area - old_area) / temperature):
            heights[source] = old_height
            first, final = old_first, old_final
            total, area = old_total, old_area
    result = climb(best[1], scrambles)
    return result


def search(rows, columns, seed, restarts, verify_updates=False):
    scrambles = make_inverse_scrambles(rows, columns, seed)
    rng = random.Random(seed + 1_000_003)
    best = None
    for _ in range(restarts):
        heights = [rng.randrange(rows + 1) for _ in range(columns)]
        result = climb(heights, scrambles, verify_updates)
        if best is None or result[0] > best[0]:
            best = result
    return best


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int, default=4096)
    parser.add_argument("--columns", type=int, default=64)
    parser.add_argument("--seed", type=int, nargs="+", default=[0, 1, 2])
    parser.add_argument("--restarts", type=int, default=12)
    parser.add_argument("--anneal-steps", type=int, default=0)
    parser.add_argument("--verify-updates", action="store_true")
    parser.add_argument("--show-profile", action="store_true")
    args = parser.parse_args()
    for seed in args.seed:
        area, heights, total, moves = search(
            args.rows, args.columns, seed, args.restarts, args.verify_updates
        )
        if args.anneal_steps:
            scrambles = make_inverse_scrambles(args.rows, args.columns, seed)
            annealed = anneal(heights, scrambles, seed + 7, args.anneal_steps,
                              args.verify_updates)
            if annealed[0] > area:
                area, heights, total, moves = annealed
        print({"rows": args.rows, "columns": args.columns, "seed": seed,
               "restarts": args.restarts, "anneal_steps": args.anneal_steps,
               "area": area,
               "area_fraction": area / (args.rows * args.columns),
               "total_marks": total, "coordinate_moves": moves,
               "column_heights": heights if args.show_profile else None})
