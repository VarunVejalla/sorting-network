"""Exact reachable-state sensitivity probes for truncated and lifted sorters.

A pivotal coordinate forces every standalone exact repair's central output
to have that coordinate as an ancestor. This is a necessary condition only.
Uses no SAT solver and enumerates all Boolean inputs (at most 16 wires).
"""
import json
import numpy as np
from sorter_lift_probe import odd_even


def layers(m):
    times = [0] * m
    result = []
    for a, b in odd_even(m):
        t = max(times[a], times[b])
        while len(result) <= t:
            result.append([])
        result[t].append((a, b))
        times[a] = times[b] = t + 1
    return result


def image(m, copies, omitted, seed):
    n = m * copies
    out = np.arange(1 << n, dtype=np.uint32)
    rng = np.random.default_rng(seed)
    base = layers(m)
    for layer in base[:len(base)-omitted]:
        for a, b in layer:
            perm = np.arange(copies) if seed is None else rng.permutation(copies)
            for r, s in enumerate(perm):
                i, j = a*copies+r, b*copies+int(s)
                swap = ((out >> i) & 1) & (1 - ((out >> j) & 1))
                out ^= (swap << i) | (swap << j)
    return len(base)-omitted, {int(x) for x in out}


def probe(m, copies, omitted, seed):
    n = m * copies
    prefix_depth, reachable = image(m, copies, omitted, seed)
    # Sorted bit at index n//2 is one iff at least n-n//2 ones exist.
    threshold = n - n//2
    pivotal = {}
    width = 0
    for x in reachable:
        first_one = next((i for i in range(n) if x & (1 << i)), n)
        last_zero = next((i for i in reversed(range(n)) if not x & (1 << i)), -1)
        width = max(width, last_zero-first_one+1)
        if x.bit_count() != threshold-1:
            continue
        for i in range(n):
            if not x & (1 << i) and x | (1 << i) in reachable:
                pivotal.setdefault(i, [x, x | (1 << i)])
    h = len(pivotal)
    return dict(m=m, copies=copies, omitted=omitted, seed=seed,
                prefix_depth=prefix_depth, reachable_states=len(reachable),
                worst_uncertain_width=width, central_pivotal_count=h,
                exact_repair_depth_lower_bound=(h-1).bit_length() if h else 0,
                pivotal_witnesses=pivotal)


if __name__ == '__main__':
    configurations = [(8, 1, e, None) for e in range(4)]
    configurations += [(8, 2, e, s) for e in [0, 1] for s in [None, 0, 1, 2, 3]]
    print(json.dumps([probe(*c) for c in configurations], indent=2))
