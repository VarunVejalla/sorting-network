"""Exact finite audit of tapered frontiers and signed-debt scalar transitions.

This checks formulas over a large finite parameter range; it is not a proof of
an infinite schedule, integer ownership, or the outsider/rank invariant.
"""
from fractions import Fraction as F

Q = F
K = 64
CAP = 2**24
E_ABS = F(31, 268_369_920)
E_POS = F(1, 268_369_920)
LAMBDA = F(16, 15)
Q_END = F(-31, 2**22)
Q_MID = F(1, 2**22)
R_END = F(2047, 2**17)
R_MID = F(1, 64)
UP = F(255, 2**24)


def parity_ceil(x, parity):
    return x if x % 2 == parity % 2 else x + 1


def alpha(d, t):
    raw = max(0, (2*t - 3*d + 23)//3)
    return parity_ceil(raw, t)


def omega(t):
    return parity_ceil((t + 4)//3, t)


def tf(d):
    return 3*d - 20


def qj(j):
    return Q_END if j in (0, 63) else Q_MID


def rj(j):
    return R_END if j in (0, 63) else R_MID


def debt_step(j, e):
    return qj(j)/64 + e/4096


def top(C, e):
    return C + LAMBDA*e*C


def bottom(B, C, e):
    return B - C/CAP - LAMBDA*e*C


def ordinary_down(C, e, j):
    return (rj(j) + e/64)*C


def interior_up(C, e):
    return (UP-e)*C


def advance_down(C, e, j):
    return (F(1,64) + LAMBDA*(qj(j)+e/64))*C


def retreat_up(C, e):
    return (F(1,65536) + e/15)*C


def audit_frontier_levels(max_d=2500):
    steps = 0
    motions = {"alpha_down": 0, "alpha_up": 0,
               "omega_down": 0, "omega_up": 0,
               "interior_levels": 0, "new_alpha": 0, "new_omega": 0}
    narrow = 0
    for d in range(14, max_d+1):
        T = tf(d)
        assert alpha(d,T) == omega(T) == d-6
        for t in range(T):
            a, w = alpha(d,t), omega(t)
            an, wn = alpha(d,t+1), omega(t+1)
            assert a <= w
            assert a % 2 == w % 2 == t % 2
            assert abs(an-a) == 1 and abs(wn-w) == 1
            motions["alpha_up" if an>a else "alpha_down"] += 1
            motions["omega_up" if wn>w else "omega_down"] += 1
            assert 6*d+6*a-4*t-8 >= 34
            assert 6*d+6*w-4*t-8 >= 36
            assert an % 2 == wn % 2 == (t+1) % 2
            assert an <= wn
            # Interior levels satisfy a+1 <= ell <= w-1. Since all levels
            # have parity t+1, this is a contiguous arithmetic progression.
            first = an
            if first < a+1:
                first += 2
            last = wn
            if last > w-1:
                last -= 2
            n_interior = max(0, (last-first)//2+1) if first <= last else 0
            motions["interior_levels"] += n_interior
            low_fringe = an == a-1
            high_fringe = wn == w+1
            motions["new_alpha"] += int(low_fringe)
            motions["new_omega"] += int(high_fringe)
            # The only possible omitted levels are the moving endpoints.
            expected_first = a-1 if low_fringe else a+1
            expected_last = w+1 if high_fringe else w-1
            assert expected_first == an and expected_last == wn
            assert (wn-an)//2+1 == n_interior + int(low_fringe) + int(high_fringe)
            if w == a:
                narrow += 1
            steps += 1
    print(f"frontier levels: PASS, d=14..{max_d}; {steps:,} stage transitions")
    print("endpoint/interior counts:", motions)
    print("single-level active bands:", narrow)

def audit_exact_debt_flow():
    # Check all scalar conservation identities at exact rational sample points.
    # Since each identity is affine in B,C,e, these samples are a diagnostic,
    # not a replacement for their Lean algebraic proofs.
    samples = [F(0), E_POS, -E_ABS, E_POS/2, -E_ABS/3]
    BC = [(F(1), F(1)), (F(3,7), F(1,1024)), (F(5,3), F(7,11))]
    for e in samples:
        assert -E_ABS <= e <= E_POS
        for C,B in BC:
            adv = sum((advance_down(C,e,j) for j in range(K)), F(0))
            assert adv == top(C,e)
            assert retreat_up(C,e) + sum((ordinary_down(C,e,j) for j in range(K)), F(0)) == top(C,e)
            assert sum((retreat_up(1024*C,debt_step(j,e)) for j in range(K)), F(0)) == top(C,e)
            assert interior_up(C,e) + sum((bottom(B/64,4*C,debt_step(j,e)) for j in range(K)), F(0)) == bottom(B,C,e)

            for j in range(K):
                recv_top = advance_down(C,e,j) + sum((interior_up(4096*C,
                    debt_step(k,debt_step(j,e))) for k in range(K)), F(0))
                assert recv_top == top(4*C,debt_step(j,e))
                recv_bottom = ordinary_down(C,e,j) + sum((bottom(B/64,4096*C,
                    debt_step(k,debt_step(j,e))) for k in range(K)), F(0))
                assert recv_bottom == bottom(B,4*C,debt_step(j,e))
    print("frontier scalar conservation: PASS (exact Fraction arithmetic)")

    min_top_retreat = F(1,65536) - E_ABS/15
    min_top_advance = min(F(1,64)+LAMBDA*(Q_END-E_ABS/64),
                          F(1,64)+LAMBDA*(Q_MID-E_ABS/64))
    min_bottom_factor = 1 - F(1,CAP) - LAMBDA*E_POS
    min_down = min(R_END-E_ABS/64, R_MID-E_ABS/64)
    assert min_top_retreat > 0 and min_top_advance > 0
    assert min_bottom_factor > 0 and min_down > 0
    print("minimum normalized coefficients:")
    print("  retreat up:", min_top_retreat, float(min_top_retreat))
    print("  advance down:", min_top_advance, float(min_top_advance))
    print("  bottom mass factor:", min_bottom_factor, float(min_bottom_factor))
    print("  ordinary down:", min_down, float(min_down))


def audit_integer_parity_obstruction():
    # A split with no down-port requires its entire register to be an even
    # up-port. This flags bottom contraction as a genuine congruence condition.
    # Exhaust the possible up-port counts to verify the iff for small n.
    for n in range(32):
        possible_contraction = any(2 * up == n for up in range(n + 1))
        assert possible_contraction == (n % 2 == 0)
    print("integer parity: bottom contraction with zero down-flow requires even register size")


if __name__ == "__main__":
    audit_frontier_levels()
    audit_exact_debt_flow()
    audit_integer_parity_obstruction()
