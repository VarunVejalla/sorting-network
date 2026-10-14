"""Exact rational screen for the conditional (k,A,q)=(64,64,16) candidate.

Checks scalar budgets and the bounded-correction real-valued interior flow
arithmetic. It does not construct/prove the integer frontier schedule or the
sign-sensitive stranger-count lemma; see SUB1000-CANDIDATE.md.
"""
from fractions import Fraction as Q


K = 64
A = 64
q = 16
nu = Q(1, q)
eps_b = Q(1, 2**21)
eps_f_tail = Q(128, 4095)
mu = Q(17, 71_565_312)
delta = Q(1, 2**25)


def show(name, value):
    print(f"{name}: {value} ~= {float(value):.12g}")


def separator_certificate():
    # Variant-B two-round bound from notes/two-round/BULK2.md. All logarithms
    # below use the same rational upper bounds as bulk2_check.py.
    m = 2**34
    e1 = Q(38, 10**6)
    lam = Q(1, 80)
    ln2_hi = Q(6_931_471_808, 10**10)
    ln100_16_hi = Q(2879, 10_000)
    ln1000_16_hi = Q(4318, 10_000)
    ln_state_hi = 35 * ln2_hi + Q(1, m)
    c_lam = lam**2 * (Q(1, 2) + Q(2, 9) * lam)
    Ktail = lam * eps_b / 2 - c_lam * e1 / 2
    round1_margin = e1**2 * m - ln_state_hi - ln100_16_hi
    round2_margin = m * Ktail - ln_state_hi - ln1000_16_hi
    monotone1 = e1**2 * (m + 1)
    monotone2 = Ktail * (m + 1)
    assert round1_margin > 0
    assert round2_margin > 0
    assert monotone1 >= 1 and monotone2 >= 1
    show("round-1 exponent margin", round1_margin)
    show("round-2 exponent margin", round2_margin)
    show("round-1 monotonicity product", monotone1)
    show("round-2 monotonicity product", monotone2)


def invariant_certificate():
    # Chvatal's scalar constraints, with the equal-block drift term removed by
    # the proposed nonuniform end/interior block sizes.
    mu_fringe = Q(1, 2) * eps_f_tail * (A * nu * K - 1) / (A**2 * K**2)
    mu_top = nu / (A * K**2)
    sibling = delta * K * A**2 / (1 - (delta * K * A) ** 2)
    bulk_margin = mu * (A * nu - 1) - eps_b - mu * (
        (K - 1) * sibling + delta * A**2 * K
    )
    # Crude weighted-profile bound: charge all k child subtrees in the
    # sibling sum, rather than subtracting the distinguished path as in the
    # uniform proof. Since sum_j p_j = k, total profile capacity at each
    # descendant depth is still exactly k^h times the reference capacity.
    weighted_sibling_margin = mu * (A * nu - 1) - eps_b - mu * (
        K * sibling + delta * A**2 * K
    )
    # The two end deficits each exceed pi/2 by c/(2Q); charging both sides
    # of the generalized window estimate costs 1/Q in parent units.
    reserve = Q(1, A**2 * K**2)
    active_rounding_error = Q(69, 2**34)
    per_side_window_margin = weighted_sibling_margin - reserve - active_rounding_error
    # Bounded, address-dependent flow correction.  The proposed unequal
    # down-flow deviations from their mean are qE=-31/2^22 and qM=1/2^22.
    # If e(root)=0, define e(child_j)=q_j*C(parent)+e(parent)/K.  With
    # C(child)=A*C(parent), E=e/C obeys Echild=q_j/A+Eparent/(A*K).
    q_end = -Q(31, 2**22)
    q_mid = Q(1, 2**22)
    contraction = Q(1, A * K)
    e_abs = abs(q_end) / A / (1 - contraction)
    e_pos = q_mid / A / (1 - contraction)
    # The correction also changes each node's actual pi. Recompute the
    # two-sided endpoint residuals using the actual pi=s*C-e:
    # interior child: 1/Q + e/64; endpoint child: 1/(2Q)-31e/64.
    # The worst negative debt is on an all-end path, while positive debt is
    # bounded by the much smaller all-middle forcing.
    reserve_interior = Q(1, A**2 * K**2) + e_pos / K
    reserve_endpoint = Q(1, 2 * A**2 * K**2) + Q(31, 64) * e_abs
    corrected_reserve = max(reserve_interior, reserve_endpoint)
    balanced_flow_margin = weighted_sibling_margin - corrected_reserve - active_rounding_error
    positive_child_correction = e_pos / K
    eps_f_allow = A * nu * delta - A**2 * K * delta**2
    fringe_fraction = nu / (2 * A * K) * (1 - 1 / (A * nu * K)) / (
        1 - Q(1, (A * K) ** 2)
    )
    f_at_m = fringe_fraction * 2**34
    assert mu == mu_fringe
    assert mu <= mu_top
    assert delta * K * A < 1
    assert bulk_margin > 0
    assert weighted_sibling_margin > 0
    assert per_side_window_margin > 0
    assert balanced_flow_margin > 0
    assert e_abs < Q(255, 2**24)  # upward flow remains nonnegative
    assert e_abs / K < Q(2047, 131072)  # every corrected end down-flow stays positive
    assert active_rounding_error < bulk_margin
    assert eps_f_allow > 0
    assert f_at_m >= 92_160
    assert f_at_m >= 1 / (656 * eps_f_allow)
    show("mu (fringe cap)", mu)
    show("mu top cap", mu_top)
    show("no-slack bulk margin", bulk_margin)
    show("all-siblings weighted bulk margin", weighted_sibling_margin)
    show("per-side reserve plus rounding margin", per_side_window_margin)
    show("bounded-flow normalized absolute correction", e_abs)
    show("bounded-flow normalized positive correction", e_pos)
    show("positive correction per child output", positive_child_correction)
    show("corrected interior two-sided reserve", reserve_interior)
    show("corrected endpoint two-sided reserve", reserve_endpoint)
    show("margin after conservative balanced-flow charge", balanced_flow_margin)
    show("69-unit discrepancy at active cutoff 2^34", active_rounding_error)
    show("delta*k*A", delta * K * A)
    show("allowed fringe epsilon", eps_f_allow)
    show("available fringe rows at m=2^34", f_at_m)
    show("required rows from max(92160, 1/(656 epsF))", max(Q(92_160), 1 / (656 * eps_f_allow)))

    # Local end/middle allocation proposed to remove the equal-child drift.
    big_q = A**2 * K**2
    occupancy = 1 - Q(1, big_q)
    up = (A * nu * K - 1) / big_q
    end_down = Q(1, K) - nu / (2 * A * K)
    middle_down = Q(1, K)
    assert up == nu / (A * K) - Q(1, big_q)
    assert 2 * end_down + (K - 2) * middle_down == occupancy - up
    assert (occupancy - up) / K == Q(1, K) - nu / (A * K**2)
    show("up-flow fraction", up)
    show("end-child fraction", end_down)
    show("middle-child fraction", middle_down)

    r_bar = (2 * end_down + (K - 2) * middle_down) / K
    p_end = end_down / r_bar
    p_mid = middle_down / r_bar
    assert 2 * p_end + (K - 2) * p_mid == K
    assert r_bar / A + up * A * K == (1 - Q(1, big_q)) * nu
    assert p_end == Q(65_504, 65_535)
    assert p_mid == Q(65_536, 65_535)
    show("end capacity multiplier", p_end)
    show("middle capacity multiplier", p_mid)
    show("normalized one-level capacity identity", r_bar / A + up * A * K)


def depth_certificate():
    # k*A = 4096 = 16^3, hence three ordinary stages per tree level.
    # Each stage uses three sorts, costing 3*T(35) = 1890 layers.
    assert K * A == q**3
    stage_depth = 3 * (35 * 36 // 2)
    # Three stages cover six input bits, so the rate is 3*stage_depth/6.
    coefficient = Q(3 * stage_depth, 6)
    assert coefficient == 945
    # General capacity is N*A^i*nu^t/(A*nu*k). At t=3d-20, i=d-7
    # its exponent is 6d + 6(d-7) - 4(3d-20) - 8 = 30.
    assert 6 * 1 + 6 * (1 - 7) - 4 * (3 - 20) - 8 == 30
    show("ordinary separator depth", Q(stage_depth))
    show("conditional limsup coefficient", coefficient)


def frontier_screen():
    def parity_ceil(m, parity):
        return m if m % 2 == parity % 2 else m + 1

    def alpha(d, t):
        raw = max(0, (2 * t - 3 * d + 23) // 3)
        return parity_ceil(raw, t)

    def omega(t):
        return parity_ceil((t + 4) // 3, t)

    for d in range(14, 301):
        tf = 3 * d - 20
        for t in range(tf + 1):
            a, w = alpha(d, t), omega(t)
            assert a <= w
            # General capacity is N*A^i*nu^t/(A*nu*k); A*nu*k=2^8 here.
            assert 6 * d + 6 * a - 4 * t - 8 >= 34
            assert 6 * d + 6 * w - 4 * t - 8 >= 36
            if t < tf:
                assert abs(alpha(d, t + 1) - a) <= 1
                assert abs(omega(t + 1) - w) <= 1
        assert alpha(d, tf) == omega(tf) == d - 6
    print("parity-frontier scan: PASS for d=14..300")


if __name__ == "__main__":
    separator_certificate()
    invariant_certificate()
    depth_certificate()
    frontier_screen()
