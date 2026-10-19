#!/usr/bin/env python3
"""Re-price the sort-based design families with walk-bound separator precision (WALK-BOUND.md).

Parameter model only.  Replaces the separator precision tables of ../tapered/exchange_rate.py
(Lemma 6.1 one round, BULK2 two rounds) by the walk-bound versions of walk_precision.py, then:
  (a) the original exchange-rate model (fringe floor 92160, eps_F = 1/(656 f)) for V0 / S / L4;
  (b) the certified-route fringe floors (../lateral-repair/lateral_certfloor_model.py, no lateral).
Columns: old route vs walk bound.

Run:  python -I reprice_walk.py            (walk-bound round 2 sketch, WALK-BOUND.md)
      ROUTE=na python -I reprice_walk.py  (proved round 2, ROUND2.md; caches na_tables.npz)
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tapered"))
sys.path.insert(0, os.path.join(HERE, "..", "lateral-repair"))
sys.path.insert(0, HERE)
import exchange_rate as E  # noqa: E402
import walk_precision as WP  # noqa: E402

OLD = (E._E1.copy(), E._E2.copy())
NEW = (np.array([WP.e1_new(L) for L in E._LG]), np.array([WP.d_new(L) for L in E._LG]))


def na_tables():
    """ROUND2.md precision (NA Chernoff both rounds, n-uniform form), on a 1-bit grid, log-interpolated; cached."""
    cache = os.path.join(HERE, "na_tables.npz")
    if os.path.exists(cache):
        z = np.load(cache)
        Ls, e1, d = z["Ls"], z["e1"], z["d"]
    else:
        import na_precision as NA
        Ls, e1, d = NA.tables()
        np.savez(cache, Ls=Ls, e1=e1, d=d)
    return (np.exp(np.interp(E._LG, Ls, np.log(e1))), np.exp(np.interp(E._LG, Ls, np.log(d))))


if os.environ.get("ROUTE", "sketch") == "na":
    NEW = na_tables()


def use(tables):
    E._E1, E._E2 = tables


VAR_A = [
    ("V0  Chvatal as is", {}),
    ("S   slack removed", dict(slack=0.0)),
    ("L4  tapered L4 (dF=1/2, assumed)", dict(side=0.5, sibmult=2.0, dF=0.5, use43=False, slack=0.0)),
]


def part_a():
    print("(a) original exchange-rate model (fringe floor 92160 rows, eps_F = 1/(656 f)); two-round separator")
    print("  variant                              | old: ideal (win)   | walk bound: ideal (win)  lg m [B, F]")
    for name, kn in VAR_A:
        row = []
        for tabs in (OLD, NEW):
            use(tabs)
            P = dict(E.DEFAULT); P.update(kn)
            res = []
            for w in range(8, 30):
                b = E.best(2.0 ** -w, P, step=0.25)
                if b:
                    res.append(b)
            bi = min((E.best(2.0 ** -w, P, integer=True) for w in range(8, 30)),
                     key=lambda r: r["win"] if r else np.inf)
            b = min(res, key=lambda r: r["ideal"])
            row.append((b, bi))
        (bo, bio), (bn, bin_) = row
        print(f"  {name:36s} | {bo['ideal']:5.0f} ({bio['win']:5.0f})     | {bn['ideal']:5.0f} ({bin_['win']:5.0f})        "
              f"{bn['lgm']:5.1f} [{bn['lgm_B']:4.1f},{bn['lgm_F']:4.1f}]", flush=True)
    use(OLD)


def part_b():
    import lateral_certfloor_model as CF
    print("\n(b) certified-route fringe floors (fringe_general_screen fits), no lateral repair")
    print("  variant            | old: ideal (win) | walk bound: ideal (win)  lg m [B, F]")
    for name, kn in CF.VARIANTS:
        row = []
        for tabs in (OLD, NEW):
            use(tabs)
            P = dict(E.DEFAULT); P.update(kn)
            b = CF.best(1.0, 0, P)
            bi = CF.best(1.0, 0, P, integer=True)
            row.append((b, bi))
        (bo, bio), (bn, bin_) = row
        print(f"  {name:18s} | {bo['ideal']:5.0f} ({bio['win']:5.0f})   | {bn['ideal']:5.0f} ({bin_['win']:5.0f})        "
              f"{bn['lgm']:5.1f} [{bn['lgm_B']:4.1f},{bn['lgm_F']:4.1f}]", flush=True)
    use(OLD)


if __name__ == "__main__":
    which = sys.argv[1:] or ["a", "b"]
    if "a" in which:
        part_a()
    if "b" in which:
        part_b()
