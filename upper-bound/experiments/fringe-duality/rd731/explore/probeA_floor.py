"""Quick float probe of regime (A) at a given floor: load_merged(j, f, s, ln n0)/s for s = 1, 2, 4, ... and the
first s where it drops below f (the monotone-average closure). Usage: probeA_floor.py floor_log2 C j1/J,j2/J,..."""
import math, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..'))
import rd_sparse as A
J = 1651190.0; f = 3329.0
fl = float(sys.argv[1]); C = float(sys.argv[2])
for m in [float(x) for x in sys.argv[3].split(',')]:
    j = m * J; ln0 = max(fl * math.log(2), j / (C * J)); t = time.time()
    out = []; s = 1; worst = -1e18; closed = None
    while s <= j / f:
        L = A.load_merged(j, f, s, ln0)
        worst = max(worst, L - f * s); out.append(f"{s}:{L / s:.0f}")
        if L / s < f:
            closed = s; break
        s *= 2
    print(f"floor 2^{fl:g} C={C:g} j={m:g}J ln n0={ln0:.1f}: L/s {' '.join(out)}  closed at {closed}  worst(pow2) {worst:.4g}"
          f" allowed {m:g}  [{time.time() - t:.0f}s]", flush=True)
