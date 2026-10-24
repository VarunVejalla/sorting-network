"""b -> 0 numerics for regime (B) at the 731.25 point (floats; rd_scaled.escapes_cell pointwise, b_lo = b_hi).
Prints esc/(b/J) at fixed tau = sigma/b for b = 1e-6 ... 1e-290 (the limit-sketch table of ROUND1-ENERGY.md).
Usage: python -I bzero731.py [C] [ratio]"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import rd_scaled as S  # noqa: E402
import params731 as P  # noqa: E402

C = float(sys.argv[1]) if len(sys.argv) > 1 else 800.0
ratio = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
S.CJ = C * P.J
_o = S.n0_of_b
S.n0_of_b = lambda b, nm=2.0 ** 30: _o(b, nm)
f = P.F_MIN
print(f"b -> 0 in (B): J = {P.J:.0f}, C = {C:g}, f = {f:g}, level ratio {ratio}", flush=True)
for b in (1e-6, 1e-12, 1e-24, 1e-48, 1e-96, 1e-192, 1e-290):
    row = []
    for tau in (1e-14, 1e-12, 1e-10, 3e-10, 1e-9, 1e-6, 1e-4):
        tot, e = S.escapes_cell(b, b, tau * b, tau * b, f, ratio=ratio)
        row.append(f"tau={tau:.0e}: {e / (b / P.J):9.4g}")
    print(f"b = {b:.0e}: " + "  ".join(row), flush=True)
