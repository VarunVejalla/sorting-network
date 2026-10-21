#!/usr/bin/env python3
"""Check the global prefix-defect decomposition on finite D2 flows.

This is a geometry/algebra diagnostic. Each active bag is fully sorted in
the sample update, a stronger local operation than the proposed 3-sort.
It checks the exact alignment-plus-local-defect identity and that local
prefix dominance makes every global prefix defect nonincreasing.
"""
import argparse
import random

from flow_dag import FlowDAG


def bag_keys(flow):
    return [
        (lev, idx)
        for lev in range(flow.d + 1)
        for idx in range(flow.p.k**lev)
    ]


def intervals(flow, t, key):
    lev, idx = key
    return flow.bag_intervals(flow.lookup(t, lev, idx), idx)


def coordinates(parts):
    return [wire for lo, hi in parts for wire in range(lo, hi)]


def prefix_counts(word):
    out = [0]
    for bit in word:
        out.append(out[-1] + bit)
    return out


def one_trial(depth, scale, seed):
    flow = FlowDAG(depth, scale=scale).build()
    N = flow.p.k**depth * scale
    rng = random.Random(seed)
    word = [rng.randrange(2) for _ in range(N)]  # 1 denotes a zero key
    q = sum(word)

    checks = 0
    for t, row in enumerate(flow.rows):
        keys = bag_keys(flow)
        parts = {key: coordinates(intervals(flow, t, key)) for key in keys}
        parts = {key: wires for key, wires in parts.items() if wires}
        active = {
            key for key in keys
            if (key[0] == 0 if t == 0 else
                flow.p.active(depth, key[0], t))
        }
        # These bag sets partition the physical/static wire coordinates.
        assert sorted(w for wires in parts.values() for w in wires) == list(range(N))
        part_list = list(parts.values())
        owner = [-1] * N
        masses = [sum(word[w] for w in wires) for wires in part_list]
        for i, wires in enumerate(part_list):
            for wire in wires:
                owner[wire] = i
        assert all(i >= 0 for i in owner)
        counts = [0] * len(part_list)
        minimum_sum = local = 0
        prefix = prefix_counts(word)
        for cut in range(N + 1):
            alignment = min(q, cut) - minimum_sum
            assert alignment >= 0 and local >= 0
            assert min(q, cut) - prefix[cut] == alignment + local
            checks += 1
            if cut < N:
                i = owner[cut]
                if counts[i] < masses[i]:
                    minimum_sum += 1
                    local += 1
                local -= word[cut]
                counts[i] += 1

        updated = word.copy()
        for key in active:
            wires = parts.get(key, [])
            incoming = [word[w] for w in wires]
            H = sum(incoming)
            outgoing = [1] * H + [0] * (len(wires) - H)
            assert all(
                sum(outgoing[:c]) >= sum(incoming[:c])
                for c in range(len(wires) + 1)
            )
            for wire, bit in zip(wires, outgoing):
                updated[wire] = bit

        assert sum(updated) == q
        next_prefix = prefix_counts(updated)
        assert all(min(q, cut) - next_prefix[cut] <= min(q, cut) - prefix[cut]
                   for cut in range(N + 1))
        word = updated

    return len(flow.rows), checks


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=7)
    parser.add_argument("--scales", type=int, nargs="+", default=[1, 2])
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    for depth in range(2, args.max_depth + 1):
        for scale in args.scales:
            stages, checks = one_trial(depth, scale, args.seed)
            print(
                f"d={depth} scale={scale}: {stages} stages, "
                f"{checks} global-cut decompositions and monotonicity checks passed"
            )
