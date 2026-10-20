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


def solve_Q(j, K, U, n, s2=1, eta=1e-4, centred=False):
    best = math.inf
    Ent = U * math.log(K + 1) + math.log(n / eta) + s2 * math.log(math.e * n / s2)
    # centred weights a = (z - b)_+: the duality's rho j term equals b sum a and cancels the background
    rho = 0.0 if centred else min(j, K * U) / n
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


def multi_escapes(j, n, f, s2, c_R0):
    """Escapes from s2 round-2 columns with shared round-1 mass (equal loads maximise the total).
    Low rows (< R0): source-set energy on |U| = R0 s2 sources. High rows (>= R0): each needs a round-1
    column taller than R0; a given round-2 column meets each such column at most about once, so its
    extra load is <= s_R0 (the number of tall round-1 columns)."""
    R0 = max(4, int(c_R0 * (6 * j) ** (1 / 3)))
    Q = solve_Q(j, R0, R0 * s2, n, s2)
    # s2 columns with W low rows each: s2 W(W+1)(2W+1)/6 <= Q
    W = 0
    while s2 * (W + 1) * (W + 2) * (2 * W + 3) / 6 <= Q:
        W += 1
    s_R0 = 9.0 * j / R0 ** 2
    b = j / n
    return s2 * max(0.0, b + W + 1.5 * s_R0 + 2 - f)


print("\nMulti-column escapes at the 731.25 fringe f = 3900 (need < j/J):")
for n_ in (2 ** 20, 2 ** 26):
    f = 3900
    jmax = 0.125 * f * n_
    print(f" n = 2^{int(math.log2(n_))}, jmax = {jmax / J:.0f} J")
    for mult in (1, 10, 40, 100, 300, 1000, 3000, 10000, 19000):
        j = mult * J
        if j > jmax:
            continue
        worst = max(((min(multi_escapes(j, n_, f, s2, c) for c in (1.0, 1.5, 2.0, 3.0)), s2)
                     for s2 in (1, 2, 4, 8, 16, 64, 256, 1024, 4096)), key=lambda r: r[0])
        print(f"   j = {mult:5g} J: worst escapes {worst[0]:9.1f} at s2 = {worst[1]:5d}  vs allowed {j / J:7.1f}"
              f"  {'OK' if worst[0] < j / J else 'FAIL'}")


def multi_level_load(j, n, s2, R0, ratio=2.0):
    """Per-column load from geometric row levels [R_i, R_{i+1}): each level's rows need z > R_i, cost
    >= sum (r+1)^2 over the counted rows; level i uses the source-set energy on |U| = (R_{i+1}-R_i) s2
    sources with weights capped at R_{i+1}. Returns the low-rows count W plus the summed high levels."""
    K = int(3 * math.sqrt(j)) + 10
    Q0 = solve_Q(j, R0, R0 * s2, n, s2, centred=True)
    W = 0
    while s2 * (W + 1) * (W + 2) * (2 * W + 3) / 6 <= Q0:
        W += 1
    total = W
    lo = R0
    while lo < K:
        hi = min(K, int(lo * ratio) + 1)
        Q = solve_Q(j, hi, (hi - lo) * s2, n, s2, centred=True)
        # rows counted at this level each cost >= (lo+1)^2 (weights capped at hi): count <= Q / (s2 (lo+1)^2)
        total += min(hi - lo, Q / (s2 * (lo + 1) ** 2))
        lo = hi
    return total


def multi_escapes_ml(j, n, f, s2, c_R0):
    R0 = max(4, int(c_R0 * (6 * j / max(1, s2)) ** (1 / 3)))
    b = j / n
    return s2 * max(0.0, b + multi_level_load(j, n, s2, R0) - f)


print("\nMulti-level split, escapes at f = 3900 (need < j/J):")
for n_ in (2 ** 20, 2 ** 26, 2 ** 34):
    f = 3900
    jmax = 0.125 * f * n_
    print(f" n = 2^{int(math.log2(n_))}, jmax = {jmax / J:.0f} J")
    for mult in (1, 10, 100, 300, 1000, 3000, 10000, 19000, 1e5, 1e6):
        j = mult * J
        if j > jmax:
            continue
        worst = max(((min(multi_escapes_ml(j, n_, f, s2, c) for c in (1.0, 1.5, 2.0, 3.0)), s2)
                     for s2 in (1, 4, 16, 64, 256, 1024, 4096)), key=lambda r: r[0])
        print(f"   j = {mult:8g} J (b = {j / n_:6.1f}): worst escapes {worst[0]:10.1f} at s2 = {worst[1]:5d}"
              f"  vs allowed {j / J:9.1f}  {'OK' if worst[0] < j / J else 'FAIL'}")
