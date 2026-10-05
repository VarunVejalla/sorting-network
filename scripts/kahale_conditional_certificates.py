"""Exact baseline-conditioned certificate cost on actual small prefixes."""
import argparse
from fractions import Fraction
import json

from kahale_face_matrix import catalogue
from kahale_layer_occupation import matchings


def probe(n):
    states, _, parents, _, complete = catalogue(n, 200000, 0)
    assert complete
    full = (1 << n) - 1
    costs = {}

    def cost(f):
        if f not in costs:
            one, zero = [n + 1] * (1 << n), [n + 1] * (1 << n)
            for subset in range(1 << n):
                if (f >> subset) & 1:
                    one[subset] = subset.bit_count()
                if not (f >> (full ^ subset)) & 1:
                    zero[subset] = subset.bit_count()
                for i in range(n):
                    if subset & (1 << i):
                        one[subset] = min(one[subset], one[subset ^ (1 << i)])
                        zero[subset] = min(zero[subset], zero[subset ^ (1 << i)])
            sizes = [one[x] if (f >> x) & 1 else zero[full ^ x] for x in range(1 << n)]
            assert max(sizes) <= n
            costs[f] = sum(sizes)
        return costs[f]

    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return result[::-1]

    best = Fraction(0)
    witness = None
    queries = 0
    layers = [layer for layer in matchings(list(range(n))) if layer]
    for source, state in enumerate(states):
        before = sum(cost(f) for f in state)
        for layer in layers:
            out = list(state)
            for a, b in layer:
                out[a], out[b] = state[a] & state[b], state[a] | state[b]
            after = sum(cost(f) for f in out)
            ratio = Fraction(after, before)
            queries += 1
            if ratio > best:
                best = ratio
                witness = dict(prefix=path(source), layer=layer,
                               before_sum_over_all_inputs=before,
                               after_sum_over_all_inputs=after, ratio=str(ratio))
    return dict(wires=n, reachable_states=len(states), complete=complete,
                layer_queries=queries, maximum_layer_ratio=str(best),
                exceeds_five_fourths=best > Fraction(5, 4), witness=witness,
                status="Exact finite certificate minimization; no universal growth bound")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5), default=5)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))
