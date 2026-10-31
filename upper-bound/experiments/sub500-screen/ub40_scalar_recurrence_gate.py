#!/usr/bin/env python3
"""Scalar Lemma 4.3' gate for UB-40 periodic restoration (model, not a proof).

Reproduces whether a relaxed order-0 outsider bound can be restored by a block
of precise stages at the screened (4,6,3) schedule. Uses screen.py's cached
walk table and schedule optimizer; no files are generated.
"""
import importlib.util
import math
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("screen", os.path.join(HERE, "screen.py"))
screen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(screen)

P, q_prec = 8, 24
row = screen.sweep({"tol": 1000.0, "split": True, "stage": "periodic",
                    "P": P, "q_prec": q_prec})
assert row is not None
k, A, nu = 2**row["x"], 2**row["y"], 2.0**(-row["z"])
delta, Anu = row["d"], A * nu
sib = delta * k * A * A / (1 - delta**2 * k**2 * A * A)
# Lemma 4.3': coefficients of the input outsider parameter and fresh error.
lam = (1 + (k - 1) * sib + delta * A * A * k) / Anu
rstar = (k - 1) / (2 * A * A * k * k)
eps_cheap = row["epsB"]
eps_precise = math.exp(float(np.interp(q_prec, screen._LS, screen._LD)))
eta = screen.ETA
fresh_cheap = (rstar + eta * eps_cheap) / Anu
fresh_precise = (rstar + eta * eps_precise) / Anu
mu = row["mu"]
pi_over_c = (Anu * k - 1) / (A * A * k * k)
# Existing Lemma 4.4 support gate: M c <= delta_F * f*n, while
# (f+1)n <= pi*c/2; use its certified delta_F=1/8.
support_cap = (1 / 8) * pi_over_c / 2
# Largest local separator error that preserves this support cap in one step.
eps_support_max = (Anu * (support_cap - lam * support_cap) - rstar) / eta
q_support_min = screen.lgm_bulk(eps_support_max, rounds=2)

def step(value, fresh):
    return lam * value + fresh


print(f"schedule=(4,6,3), cheap q={row['q']}, precise q={q_prec}")
print(f"mu={mu:.10g}, lambda={lam:.10g}, eps_cheap={eps_cheap:.10g}, "
      f"eps_precise={eps_precise:.10g}")
value = mu
for _ in range(10):
    value = step(value, fresh_cheap)
print(f"after 10 cheap: M={value:.10g}; existing support cap={support_cap:.10g}; "
      f"over cap={value / support_cap:.3f}x")
print(f"to preserve support every step: eps_B<={eps_support_max:.10g}, "
      f"bulk row exponent>={q_support_min:.3f} (integer q>=ceil={math.ceil(q_support_min)})")
for n_cheap in (1, 7, 9, 10, 16, 64):
    value = mu
    for _ in range(n_cheap):
        value = step(value, fresh_cheap)
    peak = value
    n_precise = 0
    while value > mu and n_precise < 100:
        value = step(value, fresh_precise)
        n_precise += 1
    cost = ((n_cheap * 3 * screen.S(row["q"])
             + n_precise * 3 * screen.S(q_prec))
            / (n_cheap + n_precise) * row["spb"])
    print(f"cheap={n_cheap:2d}, precise={n_precise:2d}, peak={peak:.9g}, "
          f"returned={value:.9g}, cost={cost:.2f}")
