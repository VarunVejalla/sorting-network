"""Probe which face-transport constraints require actual comparator reachability.

Enumerate monotone, weight-preserving four-bit maps, optionally enforcing
prefix dominance (ones can only move to higher-index wires). Sample larger
maps by composing embedded dominance-preserving maps. These are relaxations,
not necessarily comparator prefixes.
"""
import argparse
from itertools import combinations, product
import json
import random


def dominance(x, y, n):
    return all((y & ((1 << r) - 1)).bit_count() <=
               (x & ((1 << r) - 1)).bit_count() for r in range(1, n + 1))


def four_maps(ordered):
    pairs = list(combinations(range(4), 2))
    singles_options = [range(i, 4) if ordered else range(4) for i in range(4)]
    missing_options = [range(i + 1) if ordered else range(4) for i in range(4)]
    for singles in product(*singles_options):
        for missing in product(*missing_options):
            if any(singles[i] == missing[r] for r in range(4)
                   for i in range(4) if i != r):
                continue
            options = []
            for i, j in pairs:
                lower = (1 << singles[i]) | (1 << singles[j])
                upper = 15
                for r in range(4):
                    if r not in (i, j):
                        upper &= 15 ^ (1 << missing[r])
                options.append([y for a, b in pairs for y in [(1 << a) | (1 << b)]
                                if not lower & ~y and not y & ~upper
                                and (not ordered or dominance((1 << i) | (1 << j), y, 4))])
            for outputs in product(*options):
                v = [0] * 16
                v[15] = 15
                for i in range(4):
                    v[1 << i] = 1 << singles[i]
                    v[15 ^ (1 << i)] = 15 ^ (1 << missing[i])
                for (i, j), out in zip(pairs, outputs):
                    v[(1 << i) | (1 << j)] = out
                yield tuple(v)


class Matrix:
    def __init__(self, n):
        self.n = n
        self.pairs = list(combinations(range(n), 2))
        self.faces = [(s, s | (1 << i), s | (1 << j))
                      for s in range(1 << n) for i, j in self.pairs
                      if not s & ((1 << i) | (1 << j))]

    def signature(self, v):
        counts = [0] * ((self.n - 1) * len(self.pairs))
        pair_ids = {(1 << i) | (1 << j): r for r, (i, j) in enumerate(self.pairs)}
        for s, x, y in self.faces:
            d = v[x] ^ v[y]
            if d:
                assert d in pair_ids, "Monotone weight-preservation must leave two discrepancies"
                counts[s.bit_count() * len(self.pairs) + pair_ids[d]] += 1
        return tuple(counts)

    def gate(self, v, a, b):
        return tuple((x & ~((1 << a) | (1 << b))) |
                     (min(x >> a & 1, x >> b & 1) << a) |
                     (max(x >> a & 1, x >> b & 1) << b) for x in v)

    def witness(self, first, second):
        for a, b in self.pairs:
            x = self.signature(self.gate(first, a, b))
            y = self.signature(self.gate(second, a, b))
            if x != y:
                r = next(r for r, (u, v) in enumerate(zip(x, y)) if u != v)
                k, pair = divmod(r, len(self.pairs))
                return dict(first_map=first, second_map=second, gate=[a, b],
                            base_weight=k, pair=self.pairs[pair],
                            first_next_count=x[r], second_next_count=y[r])
        return None


def probe(n, samples):
    if n < 4 or samples < 1:
        raise ValueError("At least four wires and one sampling step are required")
    matrix = Matrix(n)
    maps = list(four_maps(True))
    rng = random.Random(0)
    states = [tuple(range(1 << n))]
    paths = [[]]
    seen = {states[0]}
    representatives = {}
    witness = None
    for step in range(samples):
        if step % 40 == 0:
            state, path = states[0], []
        wires = sorted(rng.sample(range(n), 4))
        map_id = rng.randrange(len(maps))
        local = maps[map_id]
        mask = sum(1 << i for i in wires)
        state = tuple((x & ~mask) | sum(((local[sum(((x >> i) & 1) << r
                      for r, i in enumerate(wires))] >> r) & 1) << i
                      for r, i in enumerate(wires)) for x in state)
        path = path + [dict(wires=wires, four_map=local)]
        if state in seen:
            continue
        seen.add(state)
        key = matrix.signature(state)
        first = representatives.setdefault(key, len(states))
        states.append(state)
        paths.append(path)
        if first != len(states) - 1:
            witness = matrix.witness(states[first], state)
            if witness:
                witness.update(first_construction=paths[first], second_construction=path)
                break
    # A short explicit counterexample without dominance; its provenance can
    # also be checked by the listed directed-comparator prefixes.
    directed_prefixes = [[(1, 0), (1, 2), (1, 3), (3, 2), (2, 0)],
                         [(0, 1), (0, 2), (0, 3), (3, 2), (2, 1)]]
    small = Matrix(4)
    directed_states = []
    for prefix in directed_prefixes:
        v = tuple(range(16))
        for a, b in prefix:
            v = small.gate(v, a, b)
        directed_states.append(v)
    assert small.signature(directed_states[0]) == small.signature(directed_states[1])
    directed = small.witness(*directed_states)
    assert directed is not None
    directed["prefixes_min_endpoint_first"] = directed_prefixes
    return dict(wires=n, seed=0, requested_steps=samples, steps_examined=step + 1,
                distinct_relaxed_states=len(states), four_wire_dominance_maps=len(maps),
                dominance_relaxation_counterexample=witness,
                directed_comparator_counterexample=directed,
                status="Exact finite relaxation probe; directed gates are outside the Lean Comparator type")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, default=5)
    parser.add_argument("--samples", type=int, default=30000)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires, args.samples)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))
