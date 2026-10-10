"""Exact small-network probe of pair-location discrepancy matrix closure."""
import argparse
from itertools import combinations, permutations
import json
import random


def catalogue(n, limit, random_walks):
    initial = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    states, index, parents = [initial], {initial: 0}, [None]
    gates = list(combinations(range(n), 2))
    complete = True
    for source, state in enumerate(states):
        for i, j in gates:
            out = list(state)
            out[i], out[j] = state[i] & state[j], state[i] | state[j]
            out = tuple(out)
            if out not in index:
                if len(states) >= limit:
                    complete = False
                    break
                index[out] = len(states)
                states.append(out)
                parents.append((source, (i, j)))
        if not complete:
            break
    rng = random.Random(0)
    for _ in range(random_walks):
        source = 0
        for _ in range(40):
            i, j = rng.choice(gates)
            out = list(states[source])
            out[i], out[j] = out[i] & out[j], out[i] | out[j]
            out = tuple(out)
            if out not in index:
                index[out] = len(states)
                states.append(out)
                parents.append((source, (i, j)))
            source = index[out]
    return states, index, parents, gates, complete


def probe(n, limit, random_walks):
    states, index, parents, gates, complete = catalogue(n, limit, random_walks)
    faces = [(s.bit_count(), s | (1 << i), s | (1 << j))
             for s in range(1 << n)
             for i, j in gates if not s & ((1 << i) | (1 << j))]
    slice_masks = [sum(1 << row for row, (weight, _, _) in enumerate(faces) if weight == k)
                   for k in range(n - 1)]
    input_masks = [sum(1 << x for x in range(1 << n) if x.bit_count() == k)
                   for k in range(n + 1)]
    signal_cache = {}
    signatures, means = [], []
    for state in states:
        for f in state:
            if f not in signal_cache:
                signal_cache[f] = sum((((f >> x) ^ (f >> y)) & 1) << row
                                      for row, (_, x, y) in enumerate(faces))
        diffs = [signal_cache[f] for f in state]
        counts = [(diffs[i] & diffs[j] & mask).bit_count()
                  for mask in slice_masks for i, j in gates]
        signatures.append(tuple(counts))
        means.append(tuple((f & mask).bit_count() for mask in input_masks for f in state))

    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return result[::-1]

    witnesses = {}
    classes = {}
    for enriched in (False, True):
        transitions = {}
        group_count = set()
        for source, state in enumerate(states):
            key = (signatures[source], means[source]) if enriched else signatures[source]
            group_count.add(key)
            for i, j in gates:
                out = list(state)
                out[i], out[j] = state[i] & state[j], state[i] | state[j]
                dest = index.get(tuple(out))
                if dest is None:
                    continue
                transition = key, (i, j)
                previous = transitions.get(transition)
                if previous is not None and signatures[previous[1]] != signatures[dest]:
                    old_source, old_dest = previous
                    differences = [a for a, (x, y) in enumerate(zip(signatures[old_dest], signatures[dest]))
                                   if x != y]
                    coordinate = differences[0]
                    k, pair_id = divmod(coordinate, len(gates))
                    witnesses[str(enriched)] = {
                        "first_prefix": path(old_source), "second_prefix": path(source),
                        "gate": [i, j], "base_weight": k, "pair_coordinate": gates[pair_id],
                        "first_next_count": signatures[old_dest][coordinate],
                        "second_next_count": signatures[dest][coordinate],
                        "same_all_slice_pair_matrices": True,
                        "same_all_slice_one_wire_means": means[old_source] == means[source]}
                    break
                transitions.setdefault(transition, (source, dest))
            if str(enriched) in witnesses:
                break
        classes[str(enriched)] = len(group_count)
    # Check whether observed equality is merely input-label symmetry.
    # This is a bounded diagnostic, not an orbit classification theorem.
    input_maps = [tuple(sum(((x >> i) & 1) << p[i] for i in range(n))
                        for x in range(1 << n)) for p in permutations(range(n))]
    query_order = sorted(range(1 << n), key=lambda x: (min(x.bit_count(), n - x.bit_count()), x))
    images = {}
    def image(source):
        if source not in images:
            images[source] = tuple(sum(((f >> x) & 1) << i for i, f in enumerate(states[source]))
                                   for x in range(1 << n))
        return images[source]
    representatives = {}
    checked_orbits = 0
    equivalent = 0
    nonsymmetric = None
    for source, signature in enumerate(signatures):
        if signature not in representatives:
            representatives[signature] = source
            continue
        first = representatives[signature]
        a, b = image(first), image(source)
        matched = any(all(a[mapping[x]] == b[x] for x in query_order) for mapping in input_maps)
        checked_orbits += 1
        equivalent += matched
        if not matched:
            nonsymmetric = {"first_prefix": path(first), "second_prefix": path(source)}
            break
        if checked_orbits >= 1000:
            break
    return {"wires": n, "reachable_boolean_states": len(states), "catalogue_complete": complete,
            "bfs_limit": limit, "random_walks": random_walks, "random_walk_length": 40,
            "random_seed": 0,
            "faces": len(faces), "closure_counterexamples": witnesses,
            "signature_classes_visited_before_witness": classes,
            "input_relabeling_diagnostic": {"same_matrix_pairs_checked": checked_orbits,
                                           "equivalent_under_input_relabeling": equivalent,
                                           "first_non_equivalent_pair": nonsymmetric},
            "status": "Exact Boolean executions and integer face counts; no asymptotic bound"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5, 6, 7), default=5)
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--random-walks", type=int, default=0)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires, args.limit, args.random_walks)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))
