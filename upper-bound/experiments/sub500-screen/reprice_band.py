"""Re-price the two-sort routes with a realistic repair (UB-32 band, band_adversary.py).

Two sorts with R = 0 is the one-round separator (880); a band repair of half-height W is needed, and an
actual input reaches a tail of 0.26 j / W (j <= m n / 2 by flip symmetry), i.e. 0.13 / W as a fraction of
m n. Here tail_frac is replaced by that adversarial value (a lower bound on any proof's tail), so these
costs are optimistic for every band route."""
import math
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import screen as Sc

Sc.tail_frac = lambda q, W: 0.13 / W

rows = [
    ("band (true tail)", {"stage": "band"}),
    ("band + merge first (true tail)", {"stage": "band+merge"}),
    ("band + merge + fringe /5.8 (route d)", {"stage": "band+merge", "fdiv": 5.8}),
    ("band + merge + fringe /5.8 + r* = 0", {"stage": "band+merge", "fdiv": 5.8, "rstar": 0.0}),
    ("band + merge + fringe away", {"stage": "band+merge", "split": True}),
    ("band + merge + fringe away + r* = 0", {"stage": "band+merge", "split": True, "rstar": 0.0}),
]
for name, H in rows:
    r = Sc.run(H)
    print(f"{name:45s} {r['cost'] if r else float('nan'):8.1f}  q = {r['q'] if r else '-'}  ({r['x']},{r['y']},{r['z']})" if r else name)
print("\nTolerance gates (least T with cost < 500):")
for name, H in [("band + merge + fringe /5.8", {"stage": "band+merge", "fdiv": 5.8}),
                ("band + merge + fringe /5.8 + r* = 0", {"stage": "band+merge", "fdiv": 5.8, "rstar": 0.0}),
                ("three sorts + fringe /5.8", {"fdiv": 5.8}),
                ("band + merge + fringe away", {"stage": "band+merge", "split": True})]:
    g = Sc.gate(H, "tol", 500.0)
    print(f"  {name:45s} " + (f"T >= {g[0]:.2f}  ({g[1]['cost']:.1f}, q = {g[1]['q']})" if g else "never (T <= 1e6)"))
