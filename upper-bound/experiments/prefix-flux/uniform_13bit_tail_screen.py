#!/usr/bin/env python3
"""Outward-interval screen for generic tails on the narrow uniform rectangles."""
from moderate_tail import bound, interval_envelope


def main() -> None:
    cases = {
        "mid_f15": (8190, 16384, 15),
        "botDesc_f240": (8160, 1024, 240),
    }
    for name, (m, n, f) in cases.items():
        _, theta, p0 = bound(1, f, n, m)
        upper = interval_envelope(1, f, n, m, theta, p0)
        assert 0 < upper < 1
        print(f"{name}: i=1, mass<=n; escape/n <= {float(upper):.12f} "
              f"(outward rational {upper})")


if __name__ == "__main__":
    main()
