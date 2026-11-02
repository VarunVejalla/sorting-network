#!/usr/bin/env python3
"""Search the two-round F2 certificate at small fringes.

HasPackSemanticPropertyF2 (best/AKS/Chvatal/PackSpec2.lean): for every input and
every 0 < j <= delta*f*n, fewer than eps_F*j of the j extreme keys leave the f-row
fringe. So delta = i/f for a stranger mass of i rows per column, and J = 1/eps_F.
The check is ../walk-bound/fringe_cert_v2.py, unchanged. A miss means only that
this grid did not certify the point. The largest J found is printed per point.

Any scramble pair has a floor: a column of height h after round k forces c_k(h)
keys, with c_0(h) = h and c_k(h) = sum_{r<=h} c_(k-1)(r), since each row of the
target column needs a source column at least that tall. So two rounds force an
escape from (f+1)(f+2)(f+3)/6 keys, and J cannot exceed that value.

    python d2_f2_fringe_scan.py --fringes 6 7 8
"""
import argparse
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'walk-bound'))
from fringe_cert_v2 import certify  # noqa: E402


def passes(f, J, delta):
    for g1 in range(1, f - 1):
        for g2 in range(g1 + 1, f):
            for c in (Fr(1, 3), Fr(1, 2)):
                for b in (Fr(6, 5), Fr(2), Fr(5), Fr(20), Fr(100), Fr(1000)):
                    try:
                        st = certify(f, g1, g2, c, b, J, delta)
                    except Exception:
                        continue
                    if st['exact_ok']:
                        return g1, g2, c, b
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fringes', type=int, nargs='+', default=[6, 7, 8])
    ap.add_argument('--masses', type=Fr, nargs='+',
                    default=[Fr(1, 2), Fr(1), Fr(2), Fr(4)])
    ap.add_argument('--inverse-eps', type=int, nargs='+',
                    default=[128, 64, 32, 16, 8, 4, 2])
    args = ap.parse_args()
    for f in args.fringes:
        floor = (f + 1) * (f + 2) * (f + 3) // 6
        print(f'f={f}: pyramid floor J <= {floor}', flush=True)
        for mass in args.masses:
            result = 'no witness'
            for J in args.inverse_eps:
                found = passes(f, J, mass / f)
                if found:
                    result = f'J={J} via {found}'
                    break
            print(f'  i={float(mass):.3g} delta={float(mass / f):.4f}: {result}',
                  flush=True)


if __name__ == '__main__':
    main()
