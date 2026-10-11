"""Exact adjacent-weight routing-group feasibility on reachable prefixes.

Verify baseline-conditioned certificate cores, diamond consistency, and the
per-wire adjacent-weight second-moment law. Enumerate shortest layer paths
to measure simultaneous concentration. No universal rate bound is claimed.
"""
import argparse
from collections import deque
from fractions import Fraction
from itertools import combinations
import json
from math import comb

from kahale_face_matrix import catalogue
from kahale_layer_occupation import matchings


def probe(n):
    states, index, _, gates, complete = catalogue(n, 200000, 0)
    if not complete:
        raise ValueError("This probe requires the complete reachable catalogue")
    full = (1 << n) - 1
    core_cache = {}
    certificate_bounds = {}
    graph_cache = {}

    def cores(f):
        if f not in core_cache:
            result = []
            bounds = []
            graphs = []
            for s in range(1 << n):
                if (f >> s) & 1:
                    result.append(0)
                    bounds.append((0, 0, 0))
                    graphs.append(frozenset())
                    continue
                available = full ^ s
                core = available
                minimum_certificate = n + 1
                c = available
                while True:
                    if not (f >> (full ^ c)) & 1:
                        core &= c
                        minimum_certificate = min(minimum_certificate, c.bit_count())
                    if c == 0:
                        break
                    c = (c - 1) & available
                result.append(core)
                # Two nonpivotal additions that jointly activate this wire
                # must be hit by every zero certificate valid at s.
                vertices = available & ~core
                edges = [(1 << p) | (1 << q)
                         for p, q in combinations([p for p in range(n) if vertices & (1 << p)], 2)
                         if (f >> (s | (1 << p) | (1 << q))) & 1]
                cover = vertices.bit_count()
                c = vertices
                while True:
                    if c.bit_count() < cover and all(c & edge for edge in edges):
                        cover = c.bit_count()
                    if c == 0:
                        break
                    c = (c - 1) & vertices
                lower_bound = core.bit_count() + cover
                assert lower_bound <= minimum_certificate
                bounds.append((minimum_certificate, lower_bound, len(edges)))
                graphs.append(frozenset(edges))
            core_cache[f] = result
            certificate_bounds[f] = bounds
            graph_cache[f] = graphs
        return core_cache[f]

    profiles = []
    diamond_queries = 0
    update_queries = 0
    certificate_queries, certificate_tight, certificate_strict = 0, 0, 0
    graph_update_queries = 0
    for state in states:
        outputs = [sum(((f >> x) & 1) << i for i, f in enumerate(state))
                   for x in range(1 << n)]
        labels = {}
        groups = []
        for s in range(1 << n):
            group_sets = [0] * n
            for p in range(n):
                if s & (1 << p):
                    continue
                delta = outputs[s | (1 << p)] ^ outputs[s]
                assert delta.bit_count() == 1
                i = delta.bit_length() - 1
                assert not outputs[s] & delta
                labels[s, p] = i
                group_sets[i] |= 1 << p
            assert sum(g.bit_count() for g in group_sets) == n - s.bit_count()
            for i, f in enumerate(state):
                assert group_sets[i] == cores(f)[s]
                if not (f >> s) & 1:
                    actual, bound, _ = certificate_bounds[f][s]
                    certificate_queries += 1
                    certificate_tight += actual == bound
                    certificate_strict += actual > bound
            groups.append([g.bit_count() for g in group_sets])

        coalesced = [0] * (n - 1)
        u = [[0] * n for _ in range(n)]
        square = [[0] * n for _ in range(n)]
        meet = [[0] * n for _ in range(n - 1)]
        for s in range(1 << n):
            k = s.bit_count()
            if k == n:
                continue
            r = groups[s]
            for i in range(n):
                u[k][i] += r[i]
                square[k][i] += r[i] ** 2
                if k < n - 1:
                    coalesced[k] += comb(r[i], 2)
            for p, q in combinations([p for p in range(n) if not s & (1 << p)], 2):
                a, b = labels[s, p], labels[s, q]
                c, d = labels[s | (1 << p), q], labels[s | (1 << q), p]
                if a == b:
                    assert c == d and c != a
                    meet[k][c] += 1
                else:
                    assert c == b and d == a
                diamond_queries += 1
            # Exact agreement of the meet graph with the independently
            # enumerated activation pairs of each output function.
            if k < n - 1:
                for i, f in enumerate(state):
                    expected_edges = certificate_bounds[f][s][2]
                    actual_edges = sum(labels[s | (1 << p), q] == i and labels[s, p] == labels[s, q]
                                       for p, q in combinations([p for p in range(n) if not s & (1 << p)], 2))
                    assert expected_edges == actual_edges
        for k in range(n - 1):
            for i in range(n):
                assert (k + 1) * u[k + 1][i] == (n - k) * u[k][i] - square[k][i] + 2 * meet[k][i]

        # Challenge the exact context-dependent group update for every gate.
        for a, b in gates:
            out = list(state)
            out[a], out[b] = state[a] & state[b], state[a] | state[b]
            for s in range(1 << n):
                bits = ((outputs[s] >> a) & 1, (outputs[s] >> b) & 1)
                ra, rb = groups[s][a], groups[s][b]
                expected = {(0, 0): (0, ra + rb), (0, 1): (ra, 0),
                            (1, 0): (rb, 0), (1, 1): (0, 0)}[bits]
                assert (cores(out[a])[s].bit_count(), cores(out[b])[s].bit_count()) == expected
                ca, cb = cores(state[a])[s], cores(state[b])[s]
                ga, gb = graph_cache[state[a]][s], graph_cache[state[b]][s]
                if bits == (0, 0):
                    cross = {(1 << p) | (1 << q)
                             for p in range(n) if ca & (1 << p)
                             for q in range(n) if cb & (1 << q)}
                    predicted_min = cross | {edge for edge in ga if edge & cb == edge} | {
                        edge for edge in gb if edge & ca == edge}
                    predicted_max = {edge for edge in ga | gb if not edge & (ca | cb)}
                elif bits == (0, 1):
                    predicted_min, predicted_max = ga, frozenset()
                elif bits == (1, 0):
                    predicted_min, predicted_max = gb, frozenset()
                else:
                    predicted_min, predicted_max = frozenset(), frozenset()
                assert graph_cache[out[a]][s] == predicted_min
                assert graph_cache[out[b]][s] == predicted_max
                graph_update_queries += 1
                update_queries += 1
        profiles.append(tuple(coalesced))

    totals = [comb(n, k) * comb(n - k, 2) for k in range(n - 1)]
    layers = [layer for layer in matchings(list(range(n))) if layer]
    depth = [-1] * len(states)
    parents = [None] * len(states)
    depth[0] = 0
    queue = deque([0])
    while queue:
        source = queue.popleft()
        state = states[source]
        for layer in layers:
            out = list(state)
            for a, b in layer:
                out[a], out[b] = state[a] & state[b], state[a] | state[b]
            dest = index[tuple(out)]
            if depth[dest] < 0:
                depth[dest] = depth[source] + 1
                parents[dest] = (source, layer)
                queue.append(dest)
    assert min(depth) >= 0

    def path(source):
        result = []
        while parents[source] is not None:
            source, layer = parents[source]
            result.append(layer)
        return result[::-1]

    targets = [(w,) for w in range(1, n)] + [tuple(range(w, w + 2)) for w in range(1, n - 1)]
    targets += [tuple(range(1, n))]
    targets = list(dict.fromkeys(targets))
    records = []
    for target in targets:
        best = {}
        completion = None
        for source, counts in enumerate(profiles):
            d = depth[source]
            value = min(Fraction(counts[w - 1], totals[w - 1]) for w in target)
            previous = best.get(d)
            if previous is None or value > previous[0]:
                best[d] = (value, source)
            if value == 1 and (completion is None or d < completion[0]):
                completion = (d, source)
        envelope = []
        value, source = Fraction(-1), 0
        for d in range(max(depth) + 1):
            if d in best and best[d][0] > value:
                value, source = best[d]
            envelope.append(dict(depth_at_most=d, best_minimum_coalesced_fraction=str(value)))
        records.append(dict(middle_weights=target, concentration_envelope=envelope,
                            minimum_completion_depth=completion[0],
                            shortest_completion_layers=path(completion[1])))
    return dict(wires=n, reachable_states=len(states), catalogue_complete=True,
                diamond_queries=diamond_queries, baseline_gate_update_queries=update_queries,
                certificate_cores_verified=True, adjacent_weight_second_moment_law_verified=True,
                core_plus_vertex_cover_inequality_verified=True,
                exact_meet_graph_update_queries=graph_update_queries,
                zero_output_certificate_queries=certificate_queries,
                core_plus_cover_tight_queries=certificate_tight,
                core_plus_cover_strict_queries=certificate_strict,
                depth_metric="Shortest path using arbitrary nonempty disjoint ordered-comparator layers",
                targets=records,
                status="Finite exact feasibility; no new universal amortized inequality or improved coefficient")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4, 5), default=5)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps({"wires": result["wires"], "states": result["reachable_states"],
                      "diamond_queries": result["diamond_queries"],
                      "completion_depths": [{"weights": t["middle_weights"],
                                              "depth": t["minimum_completion_depth"]}
                                             for t in result["targets"]]}, indent=2))
