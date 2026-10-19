#!/usr/bin/env python3
"""Interval-certified F2ROUND fringe (obligation 2 of README.md) at the re-priced V0 point.

Drives fringe_cert_v2.py: ../lateral-repair/fringe_cert_param.py (a faithful parametrized copy of
../../best/notes/two-round/f2round/cert.py: exact-rational preconditions, mpmath.iv outward rounding)
plus the tighter R2 tail of FRINGE-CERT.md.
A point counts only if every check passes, including 2 P1 <= 1/1000 and 2 P2 <= 1/1000 for the
per-E ("exact psi*") route.  The closed-form (Lean-friendly) checks are reported separately.

At these points EJ/D >= 2J/D >> 16, so F2ROUND's worst points n = EJ/D, (E-1)J/D, J/D are
admissible and the n >= 16 clamp of fringe_general_screen.py never activates.

Set FRINGE_DELTA (e.g. 1/8) to certify at another fringe fraction delta_F.
Usage:  python -I fringe_cert_search.py F J            (search g1, g2, c, b at fringe height F)
        python -I fringe_cert_search.py min J F0 F1   (smallest passing F in [F0, F1], bisection)
"""
import io
import os
import sys
from contextlib import redirect_stdout
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fringe_cert_v2 as FC  # noqa: E402

DELTA = Fr(os.environ.get("FRINGE_DELTA", "128/4095"))   # fringe fraction delta_F (default: the package's)
CS = [Fr(2, 5), Fr(1, 2)]


def run(f, g1, g2, c, b, J):
    try:
        with redirect_stdout(io.StringIO()):
            st = FC.certify(f, g1, g2, c, Fr(b), J, DELTA, verbose=False)
    except (AssertionError, ValueError, ZeroDivisionError, Exception) as ex:  # noqa: BLE001
        return False, ["exception: " + type(ex).__name__], None
    return st["ok"], st["fail"], st


def search(f, J, first=True):
    hits = []
    for a in (Fr(1, 5), Fr(3, 10), Fr(2, 5), Fr(1, 2)):
        for bf in (Fr(17, 20), Fr(9, 10), Fr(4, 5)):
            g1, g2 = int(a * f), int(bf * f)
            lo_b = -(-J // (g1 + 1))
            for c in CS:
                for bm in (Fr(3, 2), 3, 10, 2):
                    b = int(bm * lo_b) + 1
                    ok, fail, st = run(f, g1, g2, c, b, J)
                    exact_ok = st is not None and st["exact_ok"]
                    if exact_ok:
                        hits.append((g1, g2, c, b, ok))
                        if first:
                            return hits
    return hits


def verbose(f, g1, g2, c, b, J):
    try:
        FC.certify(f, g1, g2, c, Fr(b), J, DELTA, verbose=True)
    except Exception as ex:  # noqa: BLE001  (closed-form printout takes ln of a bogus sum once its slope check failed)
        print(f"  (closed-form printout skipped: {type(ex).__name__}; its slope checks already FAIL above)")


def main():
    a = sys.argv[1:]
    if a and a[0] == "min":
        J, lo, hi = int(a[1]), int(a[2]), int(a[3])
        assert search(hi, J), "upper end does not pass"
        while hi - lo > max(16, lo // 200):
            mid = (lo + hi) // 2
            if search(mid, J):
                hi = mid
            else:
                lo = mid
        h = search(hi, J)[0]
        print(f"J={J}: smallest certified f in bracket ~ {hi}  (fails at {lo});  g1,g2,c,b = {h[:4]}  closed-form also: {h[4]}")
        verbose(hi, *h[:4], J)
        return
    f, J = int(a[0]), int(a[1])
    h = search(f, J)
    if not h:
        print(f"f={f} J={J}: no certified parameters found")
        return
    print(f"f={f} J={J}: certified with g1,g2,c,b = {h[0][:4]}  closed-form also: {h[0][4]}")
    verbose(f, *h[0][:4], J)


if __name__ == "__main__":
    main()
