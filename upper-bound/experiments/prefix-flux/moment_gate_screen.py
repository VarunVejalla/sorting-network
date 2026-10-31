#!/usr/bin/env python3
"""Compact finite screen for terminal D2 distance moments.

This wraps sparse_probe's input-dependent rank-core oracle. It is a discovery
diagnostic, not a fixed-provider or all-input proof.
"""
import argparse
import math
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sparse_probe import probe


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--depth', type=int, default=100)
    ap.add_argument('--initial', choices=('band', 'outer', 'left', 'right', 'stripes'),
                    default='band')
    ap.add_argument('--root-eps',
                    default='1/1000000000000000000000000000000')
    args = ap.parse_args()

    d = args.depth
    N = 8192 * 8**d
    result = probe(d, 3*d, F(args.root_eps), F(19, 2000), F(1, 16),
                   F(1, 8), F(1, 3), True, args.initial, True, 8192, True,
                   (3, 3, 2), 13, True)
    if result['fail']:
        print({
            'diagnostic_only': True,
            'depth': d,
            'initial': args.initial,
            'oracle_capacity_failure': True,
            'failure_stage': result['t'],
            'failure_node': result['node'],
            'wrong_mass': result['wrong'],
            'future_capacity': result['future'],
        })
        return
    trace = result['stage_trace'] or []
    logN = math.log2(N)
    final = trace[-1]
    exponents = {
        s: math.log2(final[f'distance_moment_{s}']) / (s * logN)
        for s in (1, 2, 3) if final[f'distance_moment_{s}']
    }
    print({
        'diagnostic_only': True,
        'depth': d,
        'initial': args.initial,
        'stages': len(trace),
        'oracle_capacity_failure': result['fail'],
        'terminal': result.get('terminal'),
        'terminal_radius_exponents': exponents,
        'cleanup_coefficient_if_M3_bound_were_uniform':
            (273 + exponents[3]) / (1 - exponents[3]) if 3 in exponents else None,
    })


if __name__ == '__main__':
    main()
