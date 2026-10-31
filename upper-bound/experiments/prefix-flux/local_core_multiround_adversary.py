#!/usr/bin/env python3
"""Coordinate-ascent screen for a fixed multiround row-scramble core.

Input columns are represented by their sorted heights. Each round applies a
fixed row-wise column permutation followed by a column sort. A one-cell
change in an input height propagates along one deterministic path through all
rounds, so local ascent can evaluate and update a move in O(rounds) time.
This searches for bad profiles; it is not an all-profile certificate.
"""
import argparse
import math
import random


def make_scrambles(rows, columns, seed, rounds):
    rng = random.Random(seed)
    result = []
    for _ in range(rounds):
        stage = []
        for _row in range(rows):
            dest_to_source = rng.sample(range(columns), columns)
            source_to_dest = [0] * columns
            for dest, source in enumerate(dest_to_source):
                source_to_dest[source] = dest
            stage.append(source_to_dest)
        result.append(stage)
    return result


def area_of(final, total, columns):
    q, r = divmod(total, columns)
    balanced = (columns - r) * q * q + r * (q + 1) ** 2
    return (sum(x * x for x in final) - balanced) // 2


def evaluate(heights, scrambles):
    rows = len(scrambles[0])
    columns = len(heights)
    profiles = [heights.copy()]
    for stage in scrambles:
        after = [0] * columns
        for source, height in enumerate(profiles[-1]):
            for row in range(height):
                after[stage[row][source]] += 1
        profiles.append(after)
    total = sum(heights)
    return profiles, total, area_of(profiles[-1], total, columns)


def endpoint_after_change(source, direction, profiles, scrambles):
    for stage_index, stage in enumerate(scrambles):
        height = profiles[stage_index][source]
        row = height if direction > 0 else height - 1
        source = stage[row][source]
    return source


def apply_change(profiles, total, area, source, direction, scrambles):
    columns = len(profiles[0])
    dest = endpoint_after_change(source, direction, profiles, scrambles)
    final = profiles[-1]
    if direction > 0:
        delta = final[dest] - total // columns
    else:
        delta = (total + columns - 1) // columns - final[dest]

    profiles[0][source] += direction
    current = source
    for stage_index, stage in enumerate(scrambles):
        height = profiles[stage_index][current]
        row = height - 1 if direction > 0 else height
        dest = stage[row][current]
        profiles[stage_index + 1][dest] += direction
        current = dest
    return total + direction, area + delta


def climb(heights, scrambles, verify=False):
    rows, columns = len(scrambles[0]), len(heights)
    profiles, total, area = evaluate(heights, scrambles)
    moves = 0
    while True:
        best = (0, None)
        for source in range(columns):
            if heights[source] < rows:
                dest = endpoint_after_change(source, 1, profiles, scrambles)
                delta = profiles[-1][dest] - total // columns
                if delta > best[0]:
                    best = (delta, (source, 1))
            if heights[source] > 0:
                dest = endpoint_after_change(source, -1, profiles, scrambles)
                delta = (total + columns - 1) // columns - profiles[-1][dest]
                if delta > best[0]:
                    best = (delta, (source, -1))
        if best[1] is None:
            break
        source, direction = best[1]
        old_area = area
        total, area = apply_change(profiles, total, area, source, direction,
                                   scrambles)
        heights[source] += direction
        assert area == old_area + best[0]
        moves += 1
        if verify:
            assert evaluate(heights, scrambles) == (profiles, total, area)
    assert evaluate(heights, scrambles) == (profiles, total, area)
    return area, heights, total, moves


def anneal(heights, scrambles, seed, steps, verify=False):
    rows, columns = len(scrambles[0]), len(heights)
    rng = random.Random(seed)
    profiles, total, area = evaluate(heights, scrambles)
    best = (area, heights.copy(), total)
    start_temp = max(1.0, rows / 2)
    for step in range(steps):
        source = rng.randrange(columns)
        target = rng.randrange(rows + 1)
        if target == heights[source]:
            continue
        old_height = heights[source]
        old_profiles = [profile.copy() for profile in profiles]
        old_total, old_area = total, area
        direction = 1 if target > old_height else -1
        while heights[source] != target:
            total, area = apply_change(profiles, total, area, source,
                                       direction, scrambles)
            heights[source] += direction
        if verify:
            assert evaluate(heights, scrambles) == (profiles, total, area)
        if area > best[0]:
            best = (area, heights.copy(), total)
        temperature = start_temp * (0.01 ** (step / max(1, steps)))
        if area < old_area and rng.random() >= math.exp(
                (area - old_area) / temperature):
            heights[source] = old_height
            profiles = old_profiles
            total, area = old_total, old_area
    return climb(best[1], scrambles, verify)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int, default=4096)
    parser.add_argument("--columns", type=int, default=64)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    parser.add_argument("--restarts", type=int, default=12)
    parser.add_argument("--anneal-steps", type=int, default=0)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--show-profile", action="store_true")
    args = parser.parse_args()
    for seed in args.seeds:
        scrambles = make_scrambles(args.rows, args.columns, seed, args.rounds)
        rng = random.Random(seed + 1_000_003)
        best = None
        for _ in range(args.restarts):
            heights = [rng.randrange(args.rows + 1)
                       for _ in range(args.columns)]
            candidate = climb(heights, scrambles, args.verify)
            if best is None or candidate[0] > best[0]:
                best = candidate
        if args.anneal_steps:
            annealed = anneal(best[1], scrambles, seed + 7,
                              args.anneal_steps, args.verify)
            if annealed[0] > best[0]:
                best = annealed
        area, heights, total, moves = best
        print({"rows": args.rows, "columns": args.columns,
               "rounds": args.rounds, "seed": seed,
               "restarts": args.restarts,
               "anneal_steps": args.anneal_steps, "area": area,
               "area_fraction": area / (args.rows * args.columns),
               "total_marks": total, "coordinate_moves": moves,
               "column_heights": heights if args.show_profile else None},
              flush=True)


if __name__ == "__main__":
    main()
