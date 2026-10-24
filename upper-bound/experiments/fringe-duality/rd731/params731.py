"""Parameter point for the 731.25 route (d) fringe certificate (UB-43). See CERT-731.md.

Design P, R1 architecture, schedule (4,5,3), separator rows m in [27254890, 2^25], three full column
sorts (no band repair, so no REVIEW-v7 band-stage term). Property F: escapes < j/J for j <= jmax =
delta_F f n real keys (delta_F = 1/8), escapes = 0 (bound < 1) for j < J.
Fringe classes (f + 1 in the half-open windows):
  class A: f in [3329, 4023];  class B: f in [210012, 258047].
Columns: n >= 2^17 (Batcher threshold q = 42 at the merge-first stage depth ~920, rows <= 2^25; this also
covers the 731.25 package itself, whose threshold q = 43 gives n >= 2^18).
"""
from fractions import Fraction as Fr

J = 1651190.0          # J >= 1651190 (FRINGE-DUALITY.md, "The 731.25 point"): J = 1651190 exactly
J_FR = Fr(1651190)
CLASSES = ((3329.0, 4023.0), (210012.0, 258047.0))
F_MIN = CLASSES[0][0]
F_MAX = CLASSES[-1][1]
DELTA_F = 1.0 / 8
NMIN_LOG2 = 17


def f_eff(j_lo, n_hi):
    """least fringe f for which some class member admits mass j_lo at some column count <= n_hi, i.e. the
    worst f over all (f, n') with n' <= n_hi and j_lo <= f n'/8. Escapes decrease in f, so evaluating at
    this f bounds every admissible (f, n', j >= j_lo). Returns None if no class admits j_lo."""
    need = 8.0 * j_lo / n_hi
    for lo, hi in CLASSES:
        if need <= hi:
            return max(lo, need)
    return None


def jmax(n_hi):
    return F_MAX * n_hi / 8.0
