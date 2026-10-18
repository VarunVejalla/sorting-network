"""Numerically audit a retuned per-cut central bulk error budget.

This evaluates the informal inequalities recorded in disjoint-bulk-budget.md
and central-bulk-feasibility.md. It is a parameter screen, not a proof: the
probability adapters and integer scheduler geometry remain informal.
"""

from __future__ import annotations

import math

M_MIN = 2**42
M_MAX = 2**43
T = 2**33
F = 131040
A_LOCAL_FACTOR = 1 / 2**30
L_FACTOR = 1 / 2**18
A_WINDOW = 896
RESERVE = 128
N_MIN = 16
# Two window regions for both orientations at 63 interior cuts. The factor 2
# for U/D is already absorbed into log(2*(m+1)) in window_margin.
UNION_COUNT = 4 * 63


def profile_entropy(m: float) -> float:
    L = m * L_FACTOR
    return 1 + math.log(2 * (2 * L + 1))


def window_margin(m: float, k: int, a_window: float = A_WINDOW) -> float:
    b = (m - 2 * F) / 64
    i = F + k * b
    edge_distance = min(i, m - i)
    # The exact cut-dependent form of the protected-window exponent in
    # central-bulk-feasibility.md, less the profile/set union entropy.
    return 9 * edge_distance**2 * a_window / (32 * m * T) - math.log(2 * (m + 1))


def beta_for_budget() -> float:
    # Use only the kernel-proved lower bound epsB/2 > 1/120,000,000.
    # This leaves RESERVE counts per column at m=M_MIN and more above it.
    return 1 / 120_000_000 - 1 / 2**29 - (A_WINDOW + RESERVE) / M_MIN


def bulk_margin(m: float, beta: float) -> float:
    L = m * L_FACTOR
    rate = beta**2 * m / (2 * (L / m + beta / 3))
    return rate - profile_entropy(m)


def total_bound(m: float, beta: float) -> float:
    return beta * m + m / 2**29 + A_WINDOW


def main() -> None:
    beta = beta_for_budget()
    points = [M_MIN + (M_MAX - M_MIN) * q / 1024 for q in range(1025)]
    worst_window = min((window_margin(m, k), m, k) for m in points for k in range(1, 64))
    worst_bulk = min((bulk_margin(m, beta), m) for m in points)
    min_budget_reserve = min(m / 120_000_000 - total_bound(m, beta) for m in points)
    window_union = UNION_COUNT * math.exp(-N_MIN * worst_window[0])
    bulk_union = UNION_COUNT * math.exp(-N_MIN * worst_bulk[0])

    print(f"A_window={A_WINDOW}; reserve={RESERVE}; beta={beta:.12g}")
    print(f"sampled worst window margin={worst_window[0]:.6f} at m={worst_window[1]:.0f}, k={worst_window[2]}")
    print(f"sampled worst bulk-tail margin={worst_bulk[0]:.6f} at m={worst_bulk[1]:.0f}")
    print(f"minimum reserve below lower bound m/120000000={min_budget_reserve:.6f} per column")
    print(f"union screens at n=16: window<={window_union:.3g}; bulk<={bulk_union:.3g}")
    m = M_MIN
    print("cut-specific protected-window margins at m=2^42:")
    for k in (1, 2, 8, 16, 32, 48, 56, 62, 63):
        print(f"  k={k:2d}: {window_margin(m,k):.6f}")
    old_beta = 1 / 120_000_000 - 1 / 2**29
    old_gap_low = math.sqrt(2 * (1 + 58 * math.log(2)) / 2**58) * M_MIN / 2 - (old_beta * M_MIN + M_MIN / 2**29 + 2048)
    old_gap_high = math.sqrt(2 * (1 + 58 * math.log(2)) / 2**58) * M_MAX / 2 - (old_beta * M_MAX + M_MAX / 2**29 + 2048)
    print(f"old 2048-window budget gap at endpoints using exact epsB: {old_gap_low:.3f}, {old_gap_high:.3f}")


if __name__ == "__main__":
    main()
