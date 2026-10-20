"""Route (d) model: round-1 energy only on round-2 source sets (ROUND1-ENERGY.md).

For a round-2 target set S (size s2) the relevant sources are U = {sigma2_r^{-1}(S) : r < K}, |U| <= K s2,
K = bound on max round-1 height (~ c sqrt j). On U, with weights a = z|_U <= K and one lambda:
  Q = sum_U z^2 <= lam j + Q / (2 (lam - rho)) + sqrt(2 V Ent) + K Ent / 3,   V <= K Q / (3 lam),
  rho = sum_U a / n <= min(j, K |U|) / n,  Ent = |U| ln(K + 1) + ln(n binom(n, s2) / eta).
Then sum_{v in S} (w_v - f)_+ <= ... ; single column: W(W+1)(2W+1)/6 <= Q_b (centred at the mean b).
Prints the least f for zero escapes (single column) and the dense-regime escapes estimate.
"""
import math
import sys


def solve_Q(j, K, U, n, s2=1, eta=1e-4):
    best = math.inf
    Ent = U * math.log(K + 1) + math.log(n / eta) + s2 * math.log(math.e * n / s2)
    rho = min(j, K * U) / n
    for lam in [rho + d for d in (0.55, 0.6, 0.75, 1.0, 1.5, 2.0, 3.0)]:
        c = 1 - 1 / (2 * (lam - rho))
        if c <= 0:
            continue
        # Q c <= lam j + sqrt(2 K Q Ent / (3 lam)) + K Ent / 3: solve the quadratic in sqrt(Q)
        a_ = c
        b_ = math.sqrt(2 * K * Ent / (3 * lam))
        c_ = lam * j + K * Ent / 3
        x = (b_ + math.sqrt(b_ * b_ + 4 * a_ * c_)) / (2 * a_)
        best = min(best, x * x)
    return best


def W_of_Q(Q):
    W = 0
    while (W + 1) * (W + 2) * (2 * W + 3) / 6 <= Q:
        W += 1
    return W


n = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 ** 20
J = float(sys.argv[2]) if len(sys.argv) > 2 else 1.66e6
print(f"n = {n}, J = {J:.3g}")
for mult in (0.1, 1, 3, 10, 40, 100, 300, 800):
    j = mult * J
    b = j / n                                       # background mean height
    K = int(3 * math.sqrt(j)) + 10                  # bound on max round-1 height (round-1 single column)
    Q = solve_Q(j, K, K, n)                         # single round-2 column: |U| = K
    W = W_of_Q(Q)
    f_single = b + W                                 # zero escapes on a single column
    allowed = j / J
    print(f"  j = {mult:6g} J: b = {b:7.2f}, K = {K:6d}, Q/j = {Q / j:6.2f}, single-column load <= {f_single:8.1f}"
          f"  (escape allowance j/J = {allowed:7.1f}; need f >= {max(0, f_single - allowed):8.1f})")


def split_load(j, n, c_R0, prof_c=9.0):
    """Single round-2 column with the row split at R0: rows < R0 via the capped source-set energy,
    rows >= R0 need a round-1 column taller than R0 (at most s_R0 ~ prof_c j / R0^2 of them, each
    serving ~1 row of v: union over the tall set adds a (1 + eps) factor)."""
    R0 = max(4, int(c_R0 * (6 * j) ** (1 / 3)))
    Q = solve_Q(j, R0, R0, n)            # weights capped at R0, |U| = R0
    W_low = W_of_Q(Q)
    s_R0 = prof_c * j / R0 ** 2
    W_high = 1.5 * s_R0 + 2
    return R0, Q, W_low, W_high


print("\nRow split at R0 = c (6j)^{1/3} (low rows: capped source-set energy; high rows: tall columns):")
for n_ in (2 ** 20, 2 ** 40):
    print(f" n = 2^{int(math.log2(n_))}")
    for mult in (1, 10, 40, 100, 300, 800):
        j = mult * J
        b = j / n_
        best = min((split_load(j, n_, c) for c in (1.0, 1.5, 2.0, 3.0, 5.0)), key=lambda r: r[2] + r[3])
        R0, Q, Wl, Wh = best
        load = b + Wl + Wh
        print(f"   j = {mult:5g} J: R0 = {R0:6d}, Q/j = {Q / j:5.2f}, W_low = {Wl:6d}, W_high = {Wh:7.1f}, "
              f"load <= {load:8.1f}, need f >= {max(0, load - j / J):8.1f}  (heuristic (6j)^(1/3) + b = {(6*j)**(1/3) + b:7.1f})")
