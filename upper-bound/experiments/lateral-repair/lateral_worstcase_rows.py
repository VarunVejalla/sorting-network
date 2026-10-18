#!/usr/bin/env python3
"""Model rows at the worst-case lateral constants from LATERAL-LEMMA.md (C ~ 26 for n >= m, C ~ 44 for n = m/16).

Parameter model only.  One lateral round (R=1), no fringe band rounds.  The lemma gives total
residual <= 2(1 + sqrt(2 ln(e(1 + m/n)) + o(1))) / sqrt(lam), i.e. C = pi*(that numerator)^2/4.

Run:  python -I lateral_worstcase_rows.py [f_floor ...]
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lateral_band_model as B  # noqa: E402

E = B.E


def C_of(ratio_m_over_n):
    num = 2 * (1 + math.sqrt(2 * math.log(math.e * (1 + ratio_m_over_n))))
    return math.pi * num * num / 4


def main():
    floors = [float(a) for a in sys.argv[1:]] or [64.0, 1024.0]
    Cs = [("sims", 0.5), ("n >= m", C_of(1.0)), ("n = m/16", C_of(16.0))]
    print("worst-case constants:", ", ".join(f"{k}: C = {c:.1f}" for k, c in Cs))
    for f_floor in floors:
        print(f"\n===== f_floor = {f_floor:.0f} rows, one lateral round =====")
        for name, kn in B.VARIANTS:
            P = dict(E.DEFAULT); P.update(kn); P["f_floor"] = f_floor
            for label, C in Cs:
                b = B.best(C, 1, 0, 3.0, P)
                bi = B.best(C, 1, 0, 3.0, P, integer=True)
                wi = f"{bi['win']:5.0f}" if bi else "   - "
                print(f" {name:44s} {label:9s} C={C:5.1f} | {b['ideal']:5.0f} ({wi})  2^-{b['w']:<5.1f} rho {b['rho']:.2e} "
                      f"({b['x']:.1f},{b['y']:.1f},{b['z']:.1f})  lg m {b['lgm']:5.1f} [{b['lgm_B']:4.1f},{b['lgm_F']:4.1f}]  spb {b['spb']:.3f}",
                      flush=True)


if __name__ == "__main__":
    main()
