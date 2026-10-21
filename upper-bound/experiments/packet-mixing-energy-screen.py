#!/usr/bin/env python3
"""Screen the refined UB-25 one-cycle bulk estimate against 400 layers.

Paper-level arithmetic only. The structural rho floor comes from rank and
support; it is necessary, not an attained spectral norm. The tolerance is an
optimistic proxy imported from UB-37, not a proved UB-25 allowance.
"""
TARGET = 36 / 105_000
DEPTH_CAP = 400


def rho_floor(matchings):
    """Asymptotic lower bound for a product of pair-averaging matchings."""
    return 2 ** ((1 - matchings) / 2)


def bulk_floor(q, matchings):
    """Best possible RHS of refined energy estimate at structural rho floor."""
    rho = rho_floor(matchings)
    m = 1 << q
    return rho / 4 + matchings / (4 * m)


best = (float("inf"), None)
print(f"proxy={TARGET:.12g}; depth cap={DEPTH_CAP}")
print("q max_rounds best_rounds depth coefficient rho_floor bulk_floor rho_allowed")
for q in range(1, 101):
    max_rounds = DEPTH_CAP // (q + 1)
    candidates = [(bulk_floor(q, s), s) for s in range(1, max_rounds + 1)]
    error, s = min(candidates)
    rho = rho_floor(s)
    rho_allowed = 4 * (TARGET - s / (4 * (1 << q)))
    if error < best[0]:
        best = (error, (q, s, rho, rho_allowed))
    if q <= 20:
        print(f"{q:2d} {max_rounds:10d} {s:11d} {s*(q+1):5d} "
              f"{s*(q+1)*0.75:11.3f} {rho:10.9g} {error:.12g} "
              f"{rho_allowed:.9g}")

error, (q, s, rho, rho_allowed) = best
print(f"best over q=1..100: {error:.12g} at q={q}, s={s}")
print(f"structural rho floor={rho:.12g}; largest rho meeting proxy={rho_allowed:.12g}")
print("structural floor below proxy:", error <= TARGET)
