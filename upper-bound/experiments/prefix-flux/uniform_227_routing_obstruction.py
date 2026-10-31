#!/usr/bin/env python3
"""Reproduce the uniform-U terminal routing failure at the 227.5 candidate."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "slackfree"))
from explicit import build_table, key_sim
from flowsim import Par


def main() -> None:
    p = Par(3, 2, 2)
    depth = 5
    table, _, _ = build_table(p, depth, "U")
    trace = key_sim(p, depth, table, seed=1)
    last_stage, max_wrong_over_cap, wrong_keys = trace[-1]
    print(f"design=U, parameters=(3,2,2), depth={depth}, "
          f"stages={len(table)}, last_stage={last_stage}")
    print(f"seed=1: terminal wrong-address keys={wrong_keys}; "
          f"worst node wrong/cap={max_wrong_over_cap:.6f}")

    # D2 is the exact same schedule/flow sizes with cut-layout child blocks;
    # this control confirms that the witness is specific to uniform U routing.
    d2_table, _, _ = build_table(p, depth, "D2")
    d2_trace = key_sim(p, depth, d2_table, seed=1)
    print(f"design=D2 control: terminal wrong-address keys={d2_trace[-1][2]}")
    assert wrong_keys == 1280
    assert max_wrong_over_cap == 0.078125
    assert d2_trace[-1][2] == 0


if __name__ == "__main__":
    main()
