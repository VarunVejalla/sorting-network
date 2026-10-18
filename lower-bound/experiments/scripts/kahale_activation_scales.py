"""Exact truncated activation hypergraphs and multiscale growth screening.

Finite enumeration, not an asymptotic theorem. LP results are numerical.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
import json
import math

from kahale_face_matrix import catalogue
from kahale_layer_occupation import matchings


def probe(n):
    states, _, parents, gates, complete = catalogue(n, 200000, 0)
    assert complete
    full = (1 << n) - 1
    scales = list(range(1, n + 1))
    shift_checks = 0

    def subsets(mask):
        yield 0
        sub = mask
        while sub:
            yield sub
            sub = (sub - 1) & mask

    def minimal(edges):
        return tuple(sorted(e for e in set(edges)
                            if not any(d != e and d & e == d for d in edges)))

    @lru_cache(None)
    def activation(f, s):
        if (f >> s) & 1:
            return ()  # Only zero baselines contribute to the potential.
        return minimal([a for a in subsets(full ^ s) if (f >> (s | a)) & 1])

    @lru_cache(None)
    def profile(f):
        nonlocal shift_checks
        result = [0] * n
        for s in range(1 << n):
            if (f >> s) & 1:
                continue
            edges = activation(f, s)
            for p in range(n):
                bit = 1 << p
                if not s & bit and not (f >> (s | bit)) & 1:
                    assert activation(f, s | bit) == minimal([e & ~bit for e in edges])
                    shift_checks += 1
            candidates = list(subsets(full ^ s))
            for j, cutoff in enumerate(scales):
                truncated = [e for e in edges if e.bit_count() <= cutoff]
                result[j] += min(c.bit_count() for c in candidates
                                 if all(c & e for e in truncated))
            # Full hypergraph duality, independently using extremal inputs.
            exact = min(c.bit_count() for c in candidates
                        if not (f >> (full ^ c)) & 1)
            assert exact == min(c.bit_count() for c in candidates
                                if all(c & e for e in edges))
        return tuple(result)

    def state_profile(state):
        return tuple(sum(profile(f)[j] for f in state) for j in range(n))

    def path(source):
        out = []
        while parents[source] is not None:
            source, gate = parents[source]
            out.append(gate)
        return out[::-1]

    initial = state_profile(states[0])
    sorted_state = tuple(sum((x.bit_count() >= n-i) << x
                             for x in range(1 << n)) for i in range(n))
    terminal = state_profile(sorted_state)
    expected = tuple(sum(math.comb(n, z) * sum(z-h+1 for h in range(1, min(l,z)+1))
                         for z in range(n+1)) for l in scales)
    assert terminal == expected
    updates = 0
    for state in states:
        for a, b in gates:
            for s in range(1 << n):
                if ((state[a] | state[b]) >> s) & 1:
                    continue
                ha, hb = activation(state[a], s), activation(state[b], s)
                assert activation(state[a] & state[b], s) == minimal([e | f for e in ha for f in hb])
                assert activation(state[a] | state[b], s) == minimal(list(ha) + list(hb))
                updates += 1

    layers = [l for l in matchings(list(range(n))) if l]
    constraints = set()
    maxima = [Fraction(0)] * n
    witnesses = [None] * n
    for source, state in enumerate(states):
        before = state_profile(state)
        for layer in layers:
            out = list(state)
            for a, b in layer:
                out[a], out[b] = state[a] & state[b], state[a] | state[b]
            after = state_profile(out)
            constraints.add((before, after))
            for j in range(n):
                ratio = Fraction(after[j], before[j])
                if ratio > maxima[j]:
                    maxima[j] = ratio
                    witnesses[j] = dict(prefix=path(source), layer=layer, before=before, after=after)

    # Nonnegative combinations, normalized to sum weights one. For a fixed
    # rate rho, maximize endpoint amplification subject to every actual layer.
    import numpy as np
    from scipy.optimize import linprog
    endpoint = np.array(terminal, dtype=float) / initial[0]
    lp = []
    for rho in (1.18, 1.20, 1.22, 1.25, 1.275, 1.30, 1.40, 1.50, 2.0):
        rows = np.array([np.array(a) - rho*np.array(b) for b,a in constraints])
        fit = linprog(-endpoint, A_ub=rows, b_ub=np.zeros(len(rows)),
                      A_eq=np.ones((1,n)), b_eq=[1.0], bounds=(0,None), method="highs")
        entry = dict(rate=rho, feasible=bool(fit.success))
        if fit.success:
            amplification = float(endpoint @ fit.x)
            entry.update(weights=fit.x.tolist(), endpoint_amplification=amplification,
                         finite_depth_bound=math.log(amplification)/math.log(rho),
                         maximum_constraint_residual=float(max(rows @ fit.x)))
        lp.append(entry)
    return dict(wires=n, states=len(states), complete=complete, scales=scales,
                initial=initial, terminal=terminal, exact_hypergraph_updates=updates,
                exact_adjacent_baseline_shifts=shift_checks,
                distinct_layer_constraints=len(constraints),
                maximum_scale_ratios=[str(r) for r in maxima], witnesses=witnesses,
                numerical_nonnegative_weight_screen=lp,
                status="Exact finite hypergraph checks; numerical LP; no universal rate or improved coefficient")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, choices=(4,5), default=4)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = probe(args.wires)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps({k:v for k,v in result.items() if k != "witnesses"}, indent=2))
