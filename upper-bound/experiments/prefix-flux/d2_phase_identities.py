#!/usr/bin/env python3
"""Finite audit of the two botDesc phase identities for (3,3,2) D2.

This checks exact integer-flow identities, not sorting or a provider theorem.
The accompanying note gives the short schedule derivation and its remaining
all-depth proof obligations.
"""
from collections import Counter
from fractions import Fraction as F
import argparse

from flow_dag import FlowDAG
from oracle import Par


def audit(depth=100, scale=8192):
    p = Par(3, 3, 2)
    counts = Counter()
    d = depth
    flow = FlowDAG(d, scale=scale, p=p).build()
    for i in range(2, d):
        for t, phase in ((3 * i - 4, "strong"), (3 * i - 2, "weak")):
            if not (0 <= t < len(flow.rows)) or not p.active(d, i, t):
                continue
            assert p.role(d, i, t) == "botDesc", (d, i, t, p.role(d, i, t))
            c = scale * p.cap(d, i, t)
            for node, (a, pi, blocks) in flow.rows[t].items():
                lev, G, low, high, children = flow.nodes[node]
                if lev != i:
                    continue
                child_G = [flow.nodes[ch][1] for ch in children]
                assert len(child_G) == 8, (d, i, t, len(child_G))
                assert pi * 4096 == 15 * c, (d, i, t, "up quota")
                assert low + high == G, (d, i, t, "split deficit")
                if phase == "strong":
                    assert all(g * 128 == c for g in child_G), (d, i, t, "strong child deficits")
                    assert 16 * a == c - 16 * G, (d, i, t, "strong allocation")
                    assert blocks[0] * 8192 == 49 * c - 8192 * low
                    assert blocks[-1] * 8192 == 49 * c - 8192 * high
                    assert all(128 * b == c for b in blocks[1:-1])
                else:
                    assert all(g * 8 == c for g in child_G), (d, i, t, "weak child deficits")
                    assert a == c - G, (d, i, t, "weak allocation")
                    assert blocks[0] * 8192 == 1009 * c - 8192 * low
                    assert blocks[-1] * 8192 == 1009 * c - 8192 * high
                    assert all(8 * b == c for b in blocks[1:-1])
                counts[phase] += 1
    return counts


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=100)
    ap.add_argument("--scale", type=int, default=8192)
    args = ap.parse_args()
    counts = audit(args.depth, args.scale)
    print(f"exact compressed phase-state rows at depth {args.depth}, "
          f"scale={args.scale}: {dict(counts)}")
    print("Finite checks only; no all-depth proof or sorting bound.")
