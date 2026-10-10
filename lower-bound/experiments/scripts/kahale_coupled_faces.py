"""Four coupled Boolean executions on two-dimensional input faces.

Tracks irreversible coalescence of the two middle runs. Sampling diagnoses
the scalar barrier schedules; it does not prove a universal depth bound.
"""
import argparse
from itertools import combinations
import json
from math import log2
import random

from kahale_height_barrier import fib
from kahale_positional_barrier import layers, expand_layer


def coupled_probe(n, schedule, k, samples, seed, exact=False, repair=0):
    rng = random.Random(seed)
    base, left_delta, right_delta = [0] * n, [0] * n, [0] * n
    originals = []
    if exact:
        faces = ((s, p, q) for s in combinations(range(n), k)
                 for p, q in combinations([i for i in range(n) if i not in s], 2))
    else:
        def random_faces():
            for _ in range(samples):
                chosen = rng.sample(range(n), k + 2)
                yield chosen[2:], chosen[0], chosen[1]
        faces = random_faces()
    for row, (s, p, q) in enumerate(faces):
        mask = 1 << row
        for i in s:
            base[i] |= mask
        left_delta[p] |= mask
        right_delta[q] |= mask
        originals.append((tuple(s), p, q))
    count = len(originals)
    low = base[:]
    left = [a | b for a, b in zip(base, left_delta)]
    right = [a | b for a, b in zip(base, right_delta)]
    high = [a | b | c for a, b, c in zip(base, left_delta, right_delta)]
    alive = (1 << count) - 1
    profiles = [{"layer": 0, "uncoalesced": count}]
    first_collision = {}
    original_depth = len(schedule)
    all_layers = list(schedule) + [list(zip(range(t % 2, n - 1, 2),
                                         range(t % 2 + 1, n, 2))) for t in range(repair)]
    for t, layer in enumerate(all_layers, 1):
        killed = 0
        for i, j in layer:
            collisions = (left[i] ^ right[i]) & (left[j] ^ right[j])
            if collisions:
                # A face's two discrepancies can collide only once.
                if collisions & ~alive:
                    raise ValueError("Already coalesced face collided again")
                if (low[i] | low[j]) & collisions:
                    raise ValueError("A coalescing face must have two baseline zeros")
                if (high[i] & high[j]) & collisions != collisions:
                    raise ValueError("A coalescing face must have two upper ones")
                killed |= collisions
                if not first_collision:
                    bit = collisions & -collisions
                    first_collision = {"sample": bit.bit_length() - 1,
                                       "layer": t, "gate": [i, j]}
            for run in (low, left, right, high):
                run[i], run[j] = run[i] & run[j], run[i] | run[j]
        next_alive = 0
        for a, b in zip(left, right):
            next_alive |= a ^ b
        if next_alive != (alive & ~killed):
            raise ValueError("Coalescence differed from the exact pair collision law")
        alive = next_alive
        profiles.append({"layer": t, "uncoalesced": alive.bit_count(),
                         "new_coalescences": killed.bit_count()})
    witness = None
    if alive:
        row = (alive & -alive).bit_length() - 1
        s, p, q = originals[row]
        outputs = [[i for i in range(n) if (run[i] >> row) & 1] for run in (left, right)]
        witness = {"sample": row, "base_ones_count": len(s),
                   "base_ones_hex": hex(sum(1 << i for i in s)), "perturbed_inputs": [p, q],
                   "middle_output_difference": sorted(set(outputs[0]) ^ set(outputs[1]))}
    return {"wires": n, "depth": original_depth, "base_ones": k,
            "faces": count, "exact_enumeration": exact, "seed": seed,
            "uncoalesced_at_original_depth": profiles[original_depth]["uncoalesced"],
            "uncoalesced_fraction": profiles[original_depth]["uncoalesced"] / count,
            "repair_layers": repair, "profiles": profiles,
            "first_collision": first_collision, "surviving_face": witness}


def barrier_probe(d, fraction, samples, seed, repair):
    n = (1 << d) // ((d + 1) * fib(d + 1))
    schedule = [list(expand_layer(blocks)) for blocks in layers(n, d)]
    result = coupled_probe(n, schedule, min(n - 2, int(n * fraction)),
                           samples, seed, repair=repair)
    used = {gate for layer in schedule for gate in layer}
    result["missing_adjacent_comparators"] = sum((i, i + 1) not in used for i in range(n - 1))
    result["depth_over_log2_wires"] = d / log2(n)
    return result


def fixed_face_probe(d, repair):
    """Construct an exact surviving face from incomparable DAG vertices.

    All four original runs are fixed by the unpatched network. Adjacent
    repair rounds cannot close a pair whose initial separation exceeds twice
    their count. This is an explicit family witness, not a rate bound for
    arbitrary repairs or arbitrary sorting networks.
    """
    n = (1 << d) // ((d + 1) * fib(d + 1))
    schedule = [list(expand_layer(blocks)) for blocks in layers(n, d)]
    outgoing = [set() for _ in range(n)]
    for layer in schedule:
        for i, j in layer:
            outgoing[i].add(j)
    successors = [0] * n
    universe = (1 << n) - 1
    best = None
    for i in range(n - 1, -1, -1):
        for j in outgoing[i]:
            successors[i] |= (1 << j) | successors[j]
        missing = universe & ~((1 << (i + 1)) - 1) & ~successors[i]
        if missing:
            j = missing.bit_length() - 1
            if best is None or j - i > best[1] - best[0]:
                best = i, j
    if best is None:
        return {"depth": d, "wires": n, "incomparable_pair_found": False}
    p, q = best
    base = successors[p] | successors[q]
    if base & ((1 << p) | (1 << q)):
        raise ValueError("The pair was not incomparable")
    low, left, right, high = base, base | (1 << p), base | (1 << q), base | (1 << p) | (1 << q)
    for i, neighbors in enumerate(outgoing):
        for j in neighbors:
            for run in (low, left, right, high):
                if (run >> i) & 1 and not (run >> j) & 1:
                    raise ValueError("The constructed face was not fixed by every comparator")
    for t in range(repair):
        for i in range(t % 2, n - 1, 2):
            j = i + 1
            if (left >> i) & 1 and not (left >> j) & 1:
                left ^= (1 << i) | (1 << j)
            if (right >> i) & 1 and not (right >> j) & 1:
                right ^= (1 << i) | (1 << j)
    difference = left ^ right
    return {"depth": d, "wires": n, "incomparable_pair_found": True,
            "input_axes": [p, q], "axis_separation": q - p,
            "base_ones": base.bit_count(), "base_ones_hex": hex(base),
            "all_four_runs_fixed_by_original_network": True,
            "repair_layers": repair, "middle_runs_still_distinct": difference != 0,
            "middle_output_difference": [i for i in range(n) if (difference >> i) & 1],
            "adjacent_repair_layer_lower_bound": (q - p + 1) // 2}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, nargs="+", default=[32, 40, 48, 56])
    parser.add_argument("--samples", type=int, default=2048)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--repair", type=int, default=2)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    control_n = 8
    control = [list(zip(range(t % 2, control_n - 1, 2),
                        range(t % 2 + 1, control_n, 2))) for t in range(control_n)]
    result = {"status": "Exact local collision accounting; sampled barrier faces; no new bound",
              "sorting_control": [coupled_probe(control_n, control, k, 0, 0, exact=True)
                                  for k in range(control_n - 1)],
              "barrier": [barrier_probe(d, p, args.samples, args.seed, args.repair)
                          for d in args.depths for p in (0.25, 0.5, 0.75)],
              "exact_fixed_faces": [fixed_face_probe(d, args.repair) for d in args.depths]}
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print([(r["depth"], r["wires"], r["base_ones"], r["uncoalesced_fraction"],
            r["profiles"][-1]["uncoalesced"] / r["faces"])
           for r in result["barrier"]])
