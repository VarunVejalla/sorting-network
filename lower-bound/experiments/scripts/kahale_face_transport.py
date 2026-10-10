"""Exact context-sensitive transport probe; every queried destination is computed.

Research computation only: finite consistency does not prove matrix closure.
"""
import argparse
from itertools import combinations
import json

from kahale_face_matrix import catalogue


def probe(n, limit, walks):
    states, _, parents, gates, complete = catalogue(n, limit, walks)
    faces = [(s, s | (1 << i), s | (1 << j))
             for s in range(1 << n) for i, j in gates
             if not s & ((1 << i) | (1 << j))]
    slices = [sum(1 << r for r, (s, _, _) in enumerate(faces)
                  if s.bit_count() == k) for k in range(n - 1)]
    cache = {}

    def signals(f):
        if f not in cache:
            cache[f] = (
                sum((((f >> x) ^ (f >> y)) & 1) << r
                    for r, (_, x, y) in enumerate(faces)),
                sum(((f >> s) & 1) << r for r, (s, _, _) in enumerate(faces)))
        return cache[f]

    def signature(state):
        diffs = [signals(f)[0] for f in state]
        return tuple((diffs[i] & diffs[j] & mask).bit_count()
                     for mask in slices for i, j in gates)

    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return result[::-1]

    representatives = {}
    context_witness = None
    closure_witness = None
    equal_pairs = 0
    for source, state in enumerate(states):
        key = signature(state)
        first = representatives.setdefault(key, source)
        if first == source:
            continue
        equal_pairs += 1
        old = states[first]
        for a, b in gates:
            old_out, out = list(old), list(state)
            old_out[a], old_out[b] = old[a] & old[b], old[a] | old[b]
            out[a], out[b] = state[a] & state[b], state[a] | state[b]
            old_key, new_key = signature(old_out), signature(out)
            if old_key != new_key:
                coordinate = next(r for r, (x, y) in enumerate(zip(old_key, new_key))
                                  if x != y)
                k, pair = divmod(coordinate, len(gates))
                closure_witness = dict(first_prefix=path(first), second_prefix=path(source),
                                       gate=[a, b], base_weight=k, pair=gates[pair],
                                       first_count=old_key[coordinate], second_count=new_key[coordinate])
                break
            if context_witness is None:
                for j in range(n):
                    if j in (a, b):
                        continue
                    for axis, context in ((a, b), (b, a)):
                        for k, mask in enumerate(slices):
                            c_old = (signals(old[axis])[0] & signals(old[j])[0]
                                     & signals(old[context])[1] & mask).bit_count()
                            c_new = (signals(state[axis])[0] & signals(state[j])[0]
                                     & signals(state[context])[1] & mask).bit_count()
                            if c_old != c_new:
                                context_witness = dict(first_prefix=path(first), second_prefix=path(source),
                                                       axes=[axis, j], context_wire=context, base_weight=k,
                                                       first_count=c_old, second_count=c_new)
                                break
        if closure_witness is not None:
            break
    return dict(wires=n, states=len(states), catalogue_complete=complete,
                bfs_limit=limit, random_walks=walks, random_seed=0,
                equal_matrix_pairs_examined=equal_pairs,
                signature_classes_visited=len(representatives),
                individual_context_counterexample=context_witness,
                matrix_transition_counterexample=closure_witness,
                destination_policy="Compute every queried transition, including uncatalogued destinations",
                status="Finite exact integer computation; no universal closure theorem or improved bound")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, default=5)
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--random-walks", type=int, default=0)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires, args.limit, args.random_walks)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))
