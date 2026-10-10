"""Exact occupation/face energy ledger on actual ordered comparator prefixes.

All arithmetic is integer. The spectral nonnegativity statement has a
separate mathematical derivation; finite checks do not prove it generally.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb

from kahale_face_matrix import catalogue


def matchings(wires):
    if not wires:
        yield ()
        return
    a, *rest = wires
    yield from matchings(rest)
    for b in rest:
        remaining = [i for i in rest if i != b]
        for suffix in matchings(remaining):
            yield ((a, b),) + suffix


def probe(n, limit, walks):
    states, index, parents, gates, complete = catalogue(n, limit, walks)
    gate_ids = {gate: i for i, gate in enumerate(gates)}
    faces = [(s.bit_count() + 1, s | (1 << i), s | (1 << j))
             for s in range(1 << n) for i, j in gates if not s & ((1 << i) | (1 << j))]
    masks = [sum(1 << x for x in range(1 << n) if x.bit_count() == w)
             for w in range(1, n)]
    edge_masks = [sum(1 << r for r, (weight, _, _) in enumerate(faces) if weight == w)
                  for w in range(1, n)]
    diffs = {}
    profiles = {}

    def profile(state):
        if state not in profiles:
            for f in state:
                if f not in diffs:
                    diffs[f] = sum((((f >> x) ^ (f >> y)) & 1) << r
                                   for r, (_, x, y) in enumerate(faces))
            result = []
            for w, (mask, edges) in enumerate(zip(masks, edge_masks), 1):
                mass = comb(n, w)
                ones = [(f & mask).bit_count() for f in state]
                variance = sum(u * (mass - u) for u in ones)
                q = [(diffs[state[a]] & diffs[state[b]] & edges).bit_count()
                     for a, b in gates]
                ab = [((state[a] & ~state[b] & mask).bit_count(),
                       (state[b] & ~state[a] & mask).bit_count()) for a, b in gates]
                energy = 2 * mass * sum(q) - n * variance
                assert energy >= 0, ("spectral bound failure", state, w, energy)
                result.append(dict(mass=mass, unresolved=sum(q), variance=variance,
                                   energy=energy, q=q, orientation_counts=ab))
            profiles[state] = result
        return profiles[state]

    heights = []
    for source in range(len(states)):
        if parents[source] is None:
            heights.append((0,) * n)
        else:
            previous, (a, b) = parents[source]
            h = list(heights[previous])
            h[a], h[b] = min(h[a], h[b]), max(h[a], h[b]) + 1
            heights.append(tuple(h))

    def path(source):
        result = []
        while parents[source] is not None:
            source, gate = parents[source]
            result.append(gate)
        return result[::-1]

    layers = [layer for layer in matchings(list(range(n))) if layer]
    queries = 0
    spending_layers = 0
    efficient_spending = 0
    witness = None
    for source, state in enumerate(states):
        before = profile(state)
        for layer in layers:
            out = list(state)
            for a, b in layer:
                out[a], out[b] = state[a] & state[b], state[a] | state[b]
            after = profile(tuple(out))
            efficient = all(heights[source][a] == heights[source][b] for a, b in layer)
            for w, (old, new) in enumerate(zip(before, after), 1):
                kills = sum(old["q"][gate_ids[gate]] for gate in layer)
                products = sum(old["orientation_counts"][gate_ids[gate]][0] *
                               old["orientation_counts"][gate_ids[gate]][1] for gate in layer)
                assert new["unresolved"] == old["unresolved"] - kills
                assert new["variance"] == old["variance"] - 2 * products
                assert new["energy"] == old["energy"] - 2 * old["mass"] * kills + 2 * n * products
                queries += 1
                if new["energy"] < old["energy"]:
                    spending_layers += 1
                    if efficient:
                        efficient_spending += 1
                        if witness is None:
                            witness = dict(prefix=path(source), heights=heights[source], layer=layer,
                                           weight=w, mass=old["mass"], killed_faces=kills,
                                           orientation_products=products,
                                           energy_before=old["energy"], energy_after=new["energy"],
                                           all_comparators_equal_height=True,
                                           output_sorts_all_boolean_inputs=all(
                                               all(((out[i] >> x) & 1) <= ((out[i + 1] >> x) & 1)
                                                   for i in range(n - 1)) for x in range(1 << n)))
    # The central slice of one fully matched initial layer admits a closed
    # formula. The reserve fraction tends to 1/4; these are exact rationals.
    initial_layer_family = []
    for size in (4, 8, 16, 32, 64, 128, 256, 512):
        w = size // 2
        mass = comb(size, w)
        a = comb(size - 2, w - 1)
        energy = size * a * (size * a - mass)
        total_collision_cost = mass * mass * w * (size - w)
        fraction = Fraction(energy, total_collision_cost)
        initial_layer_family.append(dict(wires=size, weight=w,
                                         initial_reserve_fraction=str(fraction),
                                         approximate_fraction=float(fraction)))
    sorting_control = None
    if n == 4:
        state = states[0]
        h = [0] * n
        control_layers = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((1, 2),)]
        rows = []
        for layer in control_layers:
            old = profile(state)[1]  # weight two
            assert all(h[a] == h[b] for a, b in layer)
            kills = sum(old["q"][gate_ids[gate]] for gate in layer)
            products = sum(old["orientation_counts"][gate_ids[gate]][0] *
                           old["orientation_counts"][gate_ids[gate]][1] for gate in layer)
            out = list(state)
            for a, b in layer:
                out[a], out[b] = state[a] & state[b], state[a] | state[b]
                h[a], h[b] = min(h[a], h[b]), max(h[a], h[b]) + 1
            state = tuple(out)
            new = profile(state)[1]
            rows.append(dict(layer=layer, killed_faces=kills, orientation_products=products,
                             energy_before=old["energy"], energy_after=new["energy"],
                             unresolved_after=new["unresolved"], heights_after=h[:]))
        sorts = all(all(((state[i] >> x) & 1) <= ((state[i + 1] >> x) & 1)
                        for i in range(n - 1)) for x in range(1 << n))
        assert sorts
        sorting_control = dict(weight=2, mass=6, all_gates_equal_height=True,
                               sorts_all_boolean_inputs=sorts, rows=rows)
    return dict(wires=n, reachable_states=len(states), catalogue_complete=complete,
                bfs_limit=limit, random_walks=walks, random_seed=0,
                nonempty_disjoint_layers=len(layers), layer_slice_queries=queries,
                spending_layer_slice_queries=spending_layers,
                equal_height_spending_layer_slice_queries=efficient_spending,
                first_equal_height_spending_witness=witness,
                all_exact_ledgers_passed=True, all_computed_energies_nonnegative=True,
                equal_height_first_layer_reserve_family=initial_layer_family,
                four_wire_sorting_control=sorting_control,
                status="Finite actual-prefix check; no universal height tradeoff or improved coefficient")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5, 6), default=5)
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--random-walks", type=int, default=0)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires, args.limit, args.random_walks)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))
