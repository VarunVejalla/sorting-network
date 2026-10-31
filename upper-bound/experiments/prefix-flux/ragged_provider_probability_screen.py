#!/usr/bin/env python3
"""Finite parameter screen for the explicit 13-bit ragged D2 sender.

The B2 exponent uses exact rational inputs and outward interval logarithms.
The F2 calls reuse fringe_cert_v2's interval envelope; a failed parameter
point is only a failure of that certificate instance, not an impossibility.
"""
from fractions import Fraction as F
from pathlib import Path
import sys

from mpmath import iv

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "walk-bound"))
from fringe_cert_v2 import certify  # noqa: E402
from ragged_fringe_geometry import port_misalignment, realize  # noqa: E402


def main() -> None:
    m, n = 8192, 8307
    E1, d, lam = F(371, 10**8), F(3, 1250), F(1)
    K = lam * d / 2 - lam**2 * (F(1, 2) + 2 * lam / 9) * E1
    iv.dps = 60
    mK = iv.mpf(m * K.numerator) / K.denominator
    log_states = iv.log(iv.mpf(2 * (m + 1)))
    log_fail_fraction = n * (log_states - mK)
    assert log_fail_fraction.b < -866
    print(f"B2: d={d}, spill={d/2}, K={K}")
    print(f"B2: mK in [{float(mK.a):.8f},{float(mK.b):.8f}], "
          f"log states in [{float(log_states.a):.8f},{float(log_states.b):.8f}], "
          f"log failure fraction in [{float(log_fail_fraction.a):.5f},"
          f"{float(log_fail_fraction.b):.5f}]")
    print("B2: both orientations fit comfortably within a probability budget of 1/1000")

    shape = realize(67_764_224, 245_760, rows=m, tail=13)
    assert not (isinstance(shape, tuple) and isinstance(shape[0], str)), shape
    _, _, _, _, _, _, _, profile = shape
    cut_mismatch, _, port_mismatch, _, _ = port_misalignment(profile, rows=m)
    full_cut_budget = F(3, 2500) * m * n  # d=3/1250 from the B2 screen above
    transferred_cut_budget = F(1, 800) * m * n  # local epsilon_B=1/400
    assert full_cut_budget + cut_mismatch <= transferred_cut_budget
    print(f"B2 mask-transfer: max cumulative-cut mismatch={cut_mismatch}, "
          f"max single-port mismatch={port_mismatch}; "
          f"old cut budget + mismatch={full_cut_budget + cut_mismatch}, "
          f"local budget={transferred_cut_budget}")

    # Earlier, standard-ratio J=17 point. Keep it as a contrast: it does not
    # certify the actual ragged widths and does not fit the generic hf16 API.
    J = 17
    for f in (14, 15):
        g1, g2 = 2 * f // 5, 4 * f // 5
        delta = F(J + 1, f * n)
        result = certify(
            f, g1, g2, F(1, 2), 5, J, delta,
            exact_small=True, failure_budget=F(1, 10**4),
        )
        n_min = F(J, 1) / (delta * f)
        fails = ",".join(x for x in result['fail'] if x.startswith(("lambda_a", "2*P2", "closed 2*P2")))
        print(f"F2 f={f}: delta*f*n=18, n_min={float(n_min):.1f}, "
              f"hf16={result['current_hf16']}, exact={result['exact_ok']}, "
              f"closed={result['closed_ok']}; fails={fails}")

    # Shift both cuts upward and use the local rectangle dimension. The
    # closed-form (Lean-friendly) envelopes pass; only the global hf16 guard
    # remains an API mismatch.
    for f, g1, g2 in ((14, 7, 9), (15, 8, 10)):
        delta = F(18, f * n)
        result = certify(
            f, g1, g2, F(1, 3), F(6, 5), 1, delta,
            failure_budget=F(1, 1000),
        )
        assert result["exact_ok"], (f, result["fail"])
        assert not result["current_hf16"]
        assert result["closed_ok"], (f, result["fail"])
        assert F(1, 3) + F(1, 2) <= F(6, 5)  # F2Pre.hcb
        print(f"F2-local f={f}: (g1,g2)=({g1},{g2}), c=1/3, b=6/5, J=1; "
              "exact per-E=PASS, closed=PASS, hf16=FAIL")

    # Boundary-witness sensitivity: these points keep the same n and rank cap
    # but lower the nominal fringe f.  Exact=True means the per-E interval
    # envelope passes; Closed=False records the remaining Lean-friendly bound
    # gap and is not a failure of the exact numerical screen.
    for f, g1, g2, c, b, closed_expected in (
        (9, 2, 4, F(2, 5), F(1), False),
        (10, 3, 5, F(1, 3), F(6, 5), False),
        (11, 4, 6, F(1, 3), F(6, 5), True),
    ):
        delta = F(18, f * n)
        result = certify(f, g1, g2, c, b, 1, delta,
                         failure_budget=F(1, 1000))
        assert result["exact_ok"], (f, result["fail"])
        assert result["closed_ok"] == closed_expected, (f, result["fail"])
        assert not result["current_hf16"]
        print(f"F2 boundary screen f={f}: (g1,g2)=({g1},{g2}), "
              f"c={c}, b={b}, J=1; exact=PASS, "
              f"closed={'PASS' if result['closed_ok'] else 'GAP'}")

    # A rational R1b tangent bracket closes the nine-row point at n=8307.
    # This lowers the closed-screen threshold from 11 to 9; the generic hf16
    # guard still needs the local-dimension replacement.
    n9 = 8307
    f9_bracketed = certify(
        9, 2, 4, F(2, 5), F(1), 1, F(18, 9 * n9),
        failure_budget=F(1, 1000),
        r1b_bracket=(F(1527, 10000), F(1528, 10000)),
    )
    assert f9_bracketed["exact_ok"] and f9_bracketed["closed_ok"], f9_bracketed
    assert not f9_bracketed["current_hf16"]
    print("F2-local f=9, n=8307, J=1, (g1,g2,c,b)=(2,4,2/5,1), "
          "R1b bracket [1527/10000,1528/10000]: exact+closed PASS; "
          "local-dimension hf16 replacement required")

    # Conditional 13-row threshold from the corrected D2 geometry argument.
    # At n=3832, J=2 has a closed-form certificate; J=3 passes the sharper
    # per-E interval route, while the current closed R1 sum remains too loose.
    n13 = 3832
    delta13 = F(18, 13 * n13)
    f13_closed = certify(
        13, 3, 7, F(1, 4), F(2), 2, delta13,
        failure_budget=F(1, 1000),
    )
    assert f13_closed["exact_ok"] and f13_closed["closed_ok"]
    f13_tight = certify(
        13, 3, 7, F(2, 5), F(2), 3, delta13,
        failure_budget=F(1, 1000),
    )
    assert f13_tight["exact_ok"] and not f13_tight["closed_ok"]
    assert not f13_closed["current_hf16"]
    print(f"F2-local f=13, n_min={n13}, delta*f*n=18: "
          "J=2 exact+closed PASS; J=3 exact PASS, crude closed R1 GAP; "
          "local-dimension hf16 replacement required")

    # For this J=3 point, a small rational bracket around the concave R1b
    # maximizer gives a tangent certificate that closes the closed-form P1 sum.
    f13_bracketed = certify(
        13, 3, 7, F(2, 5), F(2), 3, delta13,
        failure_budget=F(1, 1000),
        r1b_bracket=(F(927, 10000), F(928, 10000)),
    )
    assert f13_bracketed["exact_ok"] and f13_bracketed["closed_ok"], f13_bracketed
    assert not f13_bracketed["current_hf16"]
    print("F2-local f=13, J=3 rational R1b bracket [927/10000,928/10000]: "
          "exact+closed PASS; local-dimension hf16 replacement required")

    # A larger support cap has substantial exact-probability slack, although
    # the current Lean-friendly closed envelope does not yet capture it.
    delta13_48 = F(48, 13 * n13)
    f13_support48 = certify(
        13, 3, 7, F(2, 5), F(2), 3, delta13_48,
        failure_budget=F(1, 1000),
    )
    assert f13_support48["exact_ok"] and not f13_support48["current_hf16"]
    print("F2-local f=13, n_min=3832, delta*f*n=48, J=3: "
          f"exact per-E={'PASS' if f13_support48['exact_ok'] else 'FAIL'}, "
          f"closed={'PASS' if f13_support48['closed_ok'] else 'GAP'}; "
          "local-dimension hf16 replacement required")

    for f, g1, g2 in ((6, 1, 2), (7, 1, 2), (8, 1, 3)):
        result = certify(f, g1, g2, F(1, 2), F(1), 1, F(18, f * n),
                         failure_budget=F(1, 1000))
        assert not result["exact_ok"], (f, result["fail"])
        print(f"F2 boundary screen f={f}: sampled point fails exact gate; "
              f"failed={','.join(result['fail'])}")


if __name__ == "__main__":
    main()



